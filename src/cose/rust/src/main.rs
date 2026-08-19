use std::{fs::File, io::{stdout, Read, Write}, path::PathBuf};

use clap::{Parser, Subcommand};
use evercosign::coseformat;
use evercosign::commonpulse;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    Sign {
        #[arg(short, long)]
        payload: PathBuf,

        #[arg(short('k'), long)]
        privkey: PathBuf,

        #[arg(short, long)]
        out_msg: PathBuf,
    },
    Verify {
        #[arg(short, long)]
        msg: PathBuf,

        #[arg(short('k'), long)]
        pubkey: PathBuf,
    },
}

use std::fmt::Display;

#[derive(Debug)]
struct NotACOSEKey {}
impl std::error::Error for NotACOSEKey {}
impl Display for NotACOSEKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

fn read_cose_key(path: PathBuf, buf: &mut Vec<u8>) -> Result<coseformat::cose_key_okp, Box<dyn std::error::Error>> {
    File::open(path)?.read_to_end(buf)?;
    match coseformat::validate_and_parse_cose_key_okp(buf.as_slice()) {
        coseformat::option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::None =>
            Err(Box::new(NotACOSEKey{})),
        coseformat::option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::Some {v: (k, _)} =>
            Ok(k),
    }
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    match cli.command {
        None => Ok(()),
        Some(Commands::Sign { payload, privkey, out_msg }) => {
            let mut payloadbuf = Vec::new();
            File::open(payload)?.read_to_end(&mut payloadbuf)?;

            let mut privkeybuf = Vec::new();
            let privkey = match read_cose_key(privkey, &mut privkeybuf)? {
                coseformat::cose_key_okp { intkeyneg4: coseformat::option__COSE_Format_bstr::Some {v: privkey}, .. } =>
                    privkey,
                _ => panic!("wrong key format"),
            };

            let mut outbuf = [0; 1024];
            let msg = commonpulse::sign1_simple(&privkey, &payloadbuf, &mut outbuf);
            File::create(out_msg)?.write_all(msg)?;

            Ok(())
        },
        Some(Commands::Verify { msg, pubkey }) => {
            let mut msgbuf = Vec::new();
            File::open(msg)?.read_to_end(&mut msgbuf)?;

            let mut pubkeybuf = Vec::new();
            let pubkey = match read_cose_key(pubkey, &mut pubkeybuf)? {
                coseformat::cose_key_okp { intkeyneg2: coseformat::option__COSE_Format_bstr::Some {v: pubkey}, .. } =>
                    pubkey,
                _ => panic!("wrong key format"),
            };

            match commonpulse::verify1_simple(pubkey, &msgbuf) {
                commonpulse::option__Pulse_Lib_Slice_slice·uint8_t::Some { v: verified_payload } => {
                    stdout().write_all(&verified_payload)?;
                    Ok(())
                },
                _ => panic!("does not verify")
            }
        },
    }
}
