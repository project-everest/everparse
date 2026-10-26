"""Inventory the public declarations of the generated runtime headers."""

import argparse
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
TOKEN = re.compile(
    r'"(?:\\.|[^"\\])*"|[A-Za-z_]\w*|'
    r"0[xX][0-9a-fA-F]+[uUlL]*|[0-9]+[uUlL]*|[^\s]"
)
IDENTIFIER = re.compile(r"[A-Za-z_]\w*\Z")


def spelling(tokens):
    return " ".join(tokens)


def parameter_type(tokens):
    if len(tokens) > 1 and IDENTIFIER.fullmatch(tokens[-1]):
        if tokens[-1] not in ("void", "char", "int", "long", "short", "unsigned"):
            tokens = tokens[:-1]
    return spelling(tokens)


def function_type(tokens):
    opening = tokens.index("(")
    name = tokens[opening - 1]
    if not IDENTIFIER.fullmatch(name) or tokens[-1] != ")":
        raise ValueError("Unsupported function declaration: " + spelling(tokens))
    result = tokens[:opening - 1]
    linkage = []
    while result and result[0] in ("static", "inline", "extern"):
        linkage.append(result.pop(0))
    arguments = tokens[opening + 1:-1]
    if any(t in ("(", ")", "[", "]", "{", "}") for t in arguments):
        raise ValueError("Unsupported parameter declaration: " + spelling(tokens))
    parameters = []
    if arguments and arguments != ["void"]:
        start = 0
        for index, token in enumerate(arguments + [","]):
            if token == ",":
                parameters.append(parameter_type(arguments[start:index]))
                start = index + 1
    return name, {
        "linkage": " ".join(linkage),
        "return": spelling(result),
        "parameters": parameters,
    }


def inventory(text):
    text = re.sub(r'/\*.*?\*/|//[^\n]*', "", text, flags=re.S)
    macros = {}
    lines = []
    for line in text.splitlines():
        if line.lstrip().startswith("#"):
            match = re.fullmatch(r"\s*#define\s+(EVERPARSE[A-Z_0-9]+)\s+(.+)", line)
            if match:
                macros[match[1]] = spelling(TOKEN.findall(match[2]))
        else:
            lines.append(line)
    text = "\n".join(lines)
    tokens = TOKEN.findall(text)
    functions = {}
    types = {}
    values = {}
    record_names = {}
    record_fields = {}
    index = 0
    linkage_depth = 0
    while index < len(tokens):
        if tokens[index:index + 3] == ["extern", '"C"', "{"]:
            linkage_depth += 1
            index += 3
            continue
        if tokens[index] == "}":
            if not linkage_depth:
                raise ValueError("Unexpected closing brace")
            linkage_depth -= 1
            index += 1
            continue
        start = index
        parens = 0
        braces = 0
        while index < len(tokens):
            token = tokens[index]
            if token == "(":
                parens += 1
            elif token == ")":
                parens -= 1
            elif token == "{":
                if (not parens and not braces
                        and tokens[start] not in ("typedef", "struct")):
                    name, declaration = function_type(tokens[start:index])
                    if name in functions and functions[name] != declaration:
                        raise ValueError("Duplicate function: " + name)
                    functions[name] = declaration
                    depth = 1
                    index += 1
                    while index < len(tokens) and depth:
                        depth += (tokens[index] == "{") - (tokens[index] == "}")
                        index += 1
                    if depth:
                        raise ValueError("Unterminated function body: " + name)
                    break
                braces += 1
            elif token == "}":
                braces -= 1
            elif token == ";" and not parens and not braces:
                declaration = tokens[start:index]
                if declaration[0] == "typedef":
                    if declaration[1] == "struct":
                        name = declaration[-1]
                        if "{" in declaration:
                            opening = declaration.index("{")
                            types[name] = {
                                "kind": "record",
                                "fields": spelling(declaration[opening + 1:-2]),
                            }
                        elif len(declaration) == 4:
                            record_names[declaration[2]] = name
                        else:
                            raise ValueError("Unsupported record alias: "
                                             + spelling(declaration))
                    elif "(" in declaration:
                        opening = declaration.index("(")
                        if declaration[opening + 1] != "*":
                            raise ValueError("Unsupported typedef: " + spelling(declaration))
                        name = declaration[opening + 2]
                        _, signature = function_type(
                            declaration[1:opening] + ["callback"]
                            + declaration[opening + 4:]
                        )
                        signature.pop("linkage")
                        types[name] = {"kind": "callback", **signature}
                    else:
                        types[declaration[-1]] = {
                            "kind": "alias", "type": spelling(declaration[1:-1]),
                        }
                elif declaration[0] == "struct" and "{" in declaration:
                    opening = declaration.index("{")
                    record_fields[declaration[1]] = spelling(
                        declaration[opening + 1:-1]
                    )
                elif "(" in declaration:
                    name, declaration = function_type(declaration)
                    if name in functions and functions[name] != declaration:
                        raise ValueError("Duplicate function: " + name)
                    functions[name] = declaration
                elif declaration[0] == "extern":
                    values[declaration[-1]] = spelling(declaration[1:-1])
                else:
                    raise ValueError("Unsupported declaration: " + spelling(declaration))
                index += 1
                break
            if parens < 0 or braces < 0:
                raise ValueError("Unbalanced declaration")
            index += 1
        else:
            raise ValueError("Unterminated declaration: " + spelling(tokens[start:]))
    for tag, name in record_names.items():
        if tag not in record_fields:
            raise ValueError("Missing record definition: " + tag)
        types[name] = {"kind": "record", "fields": record_fields.pop(tag)}
    if record_fields:
        raise ValueError("Unaliased records: " + ", ".join(record_fields))
    if linkage_depth:
        raise ValueError("Unterminated C linkage block")
    return {"functions": functions, "types": types, "values": values, "macros": macros}


def canonical_type(value):
    value = value.replace("EVERPARSE_STRING", "const char *")
    value = re.sub(r"\bBOOLEAN\b", "uint8_t", value)
    return " ".join(value.split())


def canonical_declaration(value, aliases):
    if isinstance(value, dict):
        return {k: canonical_declaration(v, aliases) for k, v in value.items()}
    if isinstance(value, list):
        return [canonical_declaration(v, aliases) for v in value]
    def expand(text, seen):
        def replace(match):
            name = match[0]
            if name not in aliases:
                return name
            if name in seen:
                raise ValueError("Cyclic ABI alias: " + name)
            return expand(aliases[name], seen | {name})
        return re.sub(r"\b[A-Za-z_]\w*\b", replace, text)
    return canonical_type(expand(value, set()))


def macro_constant(value):
    token = "".join(value.split()).replace("(", "").replace(")", "")
    match = re.fullmatch(r"([0-9]+)[uUlL]*", token)
    return int(match[1]) if match else value


def compare_abi(expected, actual):
    errors = []
    boolean = actual["types"].get("BOOLEAN")
    if boolean is not None and boolean != {"kind": "alias", "type": "uint8_t"}:
        errors.append("BOOLEAN is not a uint8_t alias")
    for category in ("functions", "types", "values", "macros"):
        for name, declaration in expected[category].items():
            found = actual[category].get(name)
            if found is None:
                errors.append("Missing " + category + " declaration: " + name)
                continue
            if category == "functions":
                declaration = dict(declaration)
                found = dict(found)
                expected_linkage = declaration.pop("linkage")
                actual_linkage = found.pop("linkage")
                if expected_linkage.startswith("static"):
                    if not actual_linkage.startswith("static"):
                        errors.append("Expected static linkage: " + name)
                elif actual_linkage != expected_linkage:
                    errors.append("Changed foreign linkage: " + name)
            if category == "macros":
                equal = macro_constant(declaration) == macro_constant(found)
            else:
                def aliases(abi):
                    return {name: ty["type"] for name, ty in abi["types"].items()
                            if ty["kind"] == "alias"}
                equal = (canonical_declaration(declaration, aliases(expected)) ==
                         canonical_declaration(found, aliases(actual)))
            if not equal:
                errors.append("Changed " + name + ": " + repr(found)
                              + ", expected " + repr(declaration))
        extras = actual[category].keys() - expected[category].keys()
        for name in sorted(extras):
            if category == "types" and name == "BOOLEAN":
                continue
            if name.startswith(("EverParse3d_", "custard_")):
                if category == "functions" and not actual[category][name]["linkage"].startswith("static"):
                    errors.append("Nonstatic implementation helper: " + name)
                continue
            errors.append("Unexpected " + category + " declaration: " + name)
    return errors


def check_headers(directory):
    contract = json.loads((HERE / "runtime-contract.json").read_text())
    reference = json.loads((HERE / "runtime-abi.json").read_text())["profiles"]
    for profile in contract["profiles"]:
        path = directory / profile["directory"] / "EverParse.h"
        text = path.read_text()
        if profile["stream"] != "buffer":
            companion = path.with_name("EverParseStreamPrimitives.h")
            # KaRaMeL's reference header has the prototypes in the main file.
            if '"EverParseStreamPrimitives.h"' in text:
                text += "\n" + companion.read_text()
        errors = compare_abi(reference[profile["directory"]], inventory(text))
        if errors:
            raise ValueError(str(path) + ":\n" + "\n".join(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--header", action="append", metavar="PROFILE=PATH")
    mode.add_argument("--check", type=Path, metavar="HEADER_ROOT")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.check:
        check_headers(args.check)
        return
    if not args.output:
        parser.error("Inventory generation requires --output")
    profiles = {}
    for argument in args.header:
        profile, path = argument.split("=", 1)
        if profile in profiles:
            parser.error("Duplicate profile: " + profile)
        profiles[profile] = inventory(Path(path).read_text())
    contract = json.loads((HERE / "runtime-contract.json").read_text())
    expected = {p["directory"] for p in contract["profiles"]}
    if profiles.keys() != expected:
        parser.error("Expected exactly the six contract profiles")
    args.output.write_text(json.dumps(
        {"schema": 1, "profiles": profiles}, indent=2, sort_keys=True
    ) + "\n")


if __name__ == "__main__":
    main()
