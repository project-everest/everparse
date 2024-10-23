#include<cstdio>
#include<cstring>
#include<iostream>
#include<algorithm>

using namespace std;

const size_t BUFFER_SIZE = 65536, NAME_SIZE = 50;

char buffer[BUFFER_SIZE], outfilename[NAME_SIZE];

unsigned read_Handshake_length_unchecked(char *s, unsigned pt, unsigned len) {
	return ((((unsigned)((unsigned char)s[pt]) << 8) | (unsigned char)s[pt + 1]) << 8) | (unsigned char)s[pt + 2];
}

unsigned jump_Handshake_tuple(char *s, unsigned pt, unsigned len) {
	if (pt + 4 > len) {
		// Not enough data
		return len;
	} else {
		return pt + 4 + (read_Handshake_length_unchecked(s, pt + 1, len));
	}
}

unsigned read_TLS_length_unchecked(char *s, unsigned pt, unsigned len) {
	return ((unsigned)((unsigned char)s[pt]) << 8) | (unsigned char)s[pt + 1];
}

unsigned jump_TLS_tuple(char *s, unsigned pt, unsigned len) {
	if (pt + 5 > len) {
		// Not enough data
		return len;
	} else {
		return pt + 5 + (read_TLS_length_unchecked(s, pt + 3, len));
	}
}

int main(int argn, char *argv[]) {
	if (argn != 2 && argn != 3) {
		printf("Usage: extract filename [output_path default=filename] \n");
		printf("       Output filenames: [output_path].n.der\n");
		return 0;
	}
	char *filename = argv[1], *outputPath = argv[2];
	FILE *TLSMessage_f= fopen(filename, "rb");
	if (TLSMessage_f) {
		unsigned len = fread(buffer, 1, BUFFER_SIZE, TLSMessage_f);
		if (!feof(TLSMessage_f)) {
			fprintf(stderr, "Error: File %s too large\n", filename);
			return -2;
		}
		fclose(TLSMessage_f);
		int cnt = 0;
		unsigned pt = 0;
		while (pt < len) {
			if (pt + 5 > len) {
				fprintf(stderr, "Error: File %s too small\n", filename);
				return -3;
			}
			if (buffer[pt] != 0x16) {
				fprintf(stderr, "Warning: Not a handshake message in file %s, ignored\n", filename);
				pt = jump_TLS_tuple(buffer, pt, len);
			} else {
				unsigned tpt = pt + 5;
				pt = jump_TLS_tuple(buffer, pt, len);
				while (tpt < pt) {
					if (tpt + 4 > pt) {
						fprintf(stderr, "Error: Failed to parse Handshake tuple\n");
						return -4;
					}
					if (buffer[tpt] != 0x0B) {
						// not a certificate message
						tpt = jump_Handshake_tuple(buffer, tpt, pt);
					} else {
						unsigned ttpt = tpt + 7;
						tpt = jump_Handshake_tuple(buffer, tpt, pt);
						while (ttpt < tpt) {
							++cnt;
							if (ttpt + 3 > tpt) {
								fprintf(stderr, "Error: Failed to parse %d-th certificate\n", cnt);
								return -5;
							}
							unsigned clen = read_Handshake_length_unchecked(buffer, ttpt, tpt);
							if (ttpt + 3 + clen > tpt) {
								fprintf(stderr, "Error: Failed to parse %d-th certificate\n", cnt);
								return -5;
							}
							if (argn == 3) {
								sprintf(outfilename, "%s.%d.der", outputPath, cnt);
							} else {
								sprintf(outfilename, "%s.%d.der", filename, cnt);
							}
							FILE *X509Output_f = fopen(outfilename, "wb");
							fwrite(buffer + ttpt + 3, 1, clen, X509Output_f);
							fclose(X509Output_f);
							ttpt += 3 + clen;
						}
					}
				}
			}
		}
		printf("Succeefully extracted %d certificates\n", cnt);
	} else {
		fprintf(stderr, "Error: File %s not found\n", filename);
		return -1;
	}
	return 0;
}
