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
    text = "\n".join(lines).replace('extern "C" {', "")
    tokens = TOKEN.findall(text)
    functions = {}
    types = {}
    values = {}
    record_names = {}
    record_fields = {}
    index = 0
    while index < len(tokens):
        if tokens[index] == "}":
            if index != len(tokens) - 1:
                raise ValueError("Unexpected closing brace")
            break
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
    return {"functions": functions, "types": types, "values": values, "macros": macros}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--header", action="append", required=True,
                        metavar="PROFILE=PATH")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
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
