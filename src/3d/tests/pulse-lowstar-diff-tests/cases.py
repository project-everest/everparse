"""Backend-independent wire cases, including the existing solver seed corpus."""

import random
import re
import struct

MAX_INPUT = 4096


def focused(function):
    name = function.replace("Validate", "Check")
    if name in {"SpecializeTaggedUnionArrayCheckMain", "SpecializeVlarrayCheckUnknownHeaders"}:
        return [(bytes(8), 8), (bytes(8), 9)]
    elf = bytearray(64)
    elf[:7] = b"\x7fELF\x02\x01\x01"
    elf[16:18] = struct.pack("<H", 1)
    elf[20:24] = struct.pack("<I", 1)
    elf[52:54] = struct.pack("<H", 64)
    tcp = bytearray(20)
    tcp[12] = 0x50
    ipv4 = b"\x45\x00\x00\x14" + bytes(16)
    examples = {
        "ElfCheckElf": (bytes(elf), 64),
        "TatMostCheckT": (struct.pack("<II", 0, 4) + bytes(4 + 2 + 4 + 1729), 0),
        "EnumerationsCheckDummy": (bytes(5) + b"\x51" + struct.pack("<I", 81), 0),
        "FieldDependence0CheckS2": (struct.pack("<HII", 0, 2, 1) + bytes(6), 0),
        "TestAllBytesCheckTest3": ((struct.pack("<I", 7) + bytes(21)) * 2 + bytes(2), 0),
        "TestSmtCheckTest1": (bytes([12, 0]), 0),
        "TestSynthetic1CheckHeader": (struct.pack("<I", 28) + bytes(24), 32),
        "Ipv6CheckIpv6Header": (b"\x60" + bytes(39), 0),
        "TcpCheckTcpHeader": (bytes(tcp), 20),
        "TestCheckT": (bytes(40) + struct.pack("<III", 5, 4, 1), 0),
        "ProbeCheckNamedPlainVariant": (struct.pack("<HH", 0, 1), 0),
        "IcmpCheckIcmpDatagram": (bytes(8), 7),
        "Ipv4CheckIpDatagramHeaderParametrized": (ipv4, 0),
        "Ipv4CheckIpv4Header": (ipv4, 0),
    }
    return [examples[name]] if name in examples else []


def seeds(path):
    text = path.read_text()
    arrays = {name: bytes(int(v.strip(), 0) for v in values.split(",") if v.strip())
              for name, values in re.findall(
                  r"static const uint8_t (\w+)\[\] = \{([^}]+)\};", text)}
    result = {}
    for function, length, name in re.findall(r'\{\s*"(\w+)"\s*,\s*(\d+)\s*,\s*(\w+)\s*\}', text):
        data = arrays[name]
        if len(data) != int(length):
            raise ValueError(f"bad checked-in seed length: {name}")
        result.setdefault(function, []).append(data)
    return result


def generate(required, seed_inputs, iterations=256):
    rng = random.Random(0x3D14)
    lines = []
    for fn_index, (fn, contract) in enumerate(required.items()):
        inputs = [bytes(n) for n in range(65)]
        inputs += [bytes(range(64)), bytes([255]) * 64]
        inputs += seed_inputs.get(fn, seed_inputs.get(fn.replace("Validate", "Check"), []))
        inputs += [bytes([3, 0, 0, 0]) + bytes(range(32)),
                   bytes([10, 0, 0, 0, 5, 0, 0, 0]),
                   bytes([1, 0, 0, 0, 2, 0, 0, 0]),
                   b"\x7fELF" + bytes([2, 1, 1]) + bytes(249)]
        for _ in range(iterations):
            n = rng.randrange(65)
            inputs.append(bytes(rng.randrange(256) for _ in range(n)))
        test_inputs = [(data, None) for data in inputs]
        for data, arg in focused(fn):
            for n in sorted({0, 1, len(data) // 2, len(data) - 1, len(data)}):
                test_inputs.append((data[:n], arg))
            test_inputs.append((data + b"\x00", arg))
        serial = 0
        for input_index, (data, fixed_arg) in enumerate(test_inputs):
            # Vary initialized scalar outputs independently from parser inputs.
            for initial in (0, 0xA5):
                arg = (0, 1, 2, 3, 4, 8, 12, 17, 18, 32, 64, 255)[input_index % 12]
                if fixed_arg is not None:
                    arg = fixed_arg
                for start in ((0, min(3, len(data))) if contract["direct"] else (0,)):
                    case = f"{fn_index}-{serial}"
                    chunk = (1, 2, 3, 4, 512)[input_index % 5]
                    # Focused witnesses need writable output capacity to reach success.
                    capacity = input_index % 4 if fixed_arg is None else 1 + input_index % 3
                    if len(data) > MAX_INPUT:
                        raise ValueError(f"{fn}: case exceeds the declared input capacity")
                    lines.append(f"{case} {fn_index} {len(data)} {arg} {initial} "
                                 f"{start} {capacity} {chunk} {data.hex() or '-'}\n")
                    serial += 1
    return "".join(lines)
