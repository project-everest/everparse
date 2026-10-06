"""Emit one identical, strictly typed driver for two generated C directories."""

import json
from pathlib import Path
import re
import subprocess

from corpus import HarnessError
from cases import MAX_INPUT

SCALARS = {"BOOLEAN", "bool", "uint8_t", "uint16_t", "uint32_t", "uint64_t",
           "int8_t", "int16_t", "int32_t", "int64_t", "size_t"}
SIG = re.compile(r"(?:^|\n)\s*(\w+(?:\s*\*)?)\s+(\w+)\s*\(([^;{}]*)\)\s*;", re.S)


def parameters(text):
    result = []
    if text.strip() in {"", "void"}:
        return result
    for part in text.split(","):
        match = re.fullmatch(r"\s*(.*?)\s*\b(\w+)\s*", part, re.S)
        if not match:
            raise HarnessError(f"unhandled public parameter declaration: {part}")
        ty = re.sub(r"\s+", " ", match[1].strip())
        ty = re.sub(r"\s*\*\s*", "*", ty)
        if not ty or "(" in ty or "[" in ty:
            raise HarnessError(f"unhandled public parameter type: {part}")
        result.append((ty, match[2]))
    return result


def signatures(path, validators=False):
    if not path.exists():
        raise HarnessError(f"missing generated public header: {path}")
    text = re.sub(r"/\*.*?\*/|//[^\n]*", "", path.read_text(), flags=re.S)
    result = {}
    for ret, name, params in SIG.findall(text):
        if validators and "Validate" not in name:
            continue
        if ret not in {"BOOLEAN", "uint64_t", "uint32_t"}:
            raise HarnessError(f"{path}: unsupported public return type {ret} for {name}")
        result[name] = (ret, parameters(params))
    return result


def check_signatures(left, right):
    if left.keys() != right.keys():
        raise HarnessError(f"public functions differ: legacy-only={sorted(left.keys()-right.keys())}, "
                           f"lowstar-only={sorted(right.keys()-left.keys())}")
    for name, (ret, params) in left.items():
        other_ret, other_params = right[name]
        if ret != other_ret or [p[0] for p in params] != [p[0] for p in other_params]:
            raise HarnessError(f"{name}: incompatible public signature: {left[name]} != {right[name]}")


def ast_fields(header, includes, clang="clang"):
    """Obtain real declared fields; never guess layouts or serialize padding."""
    command = [clang, "-x", "c", "-std=c11", "-D_DEFAULT_SOURCE",
               "-Xclang", "-ast-dump=json", "-fsyntax-only",
               *[f"-I{p}" for p in includes], str(header)]
    process = subprocess.run(command, capture_output=True, text=True)
    if process.returncode:
        raise HarnessError(f"header AST failed: {' '.join(command)}\n{process.stderr}")
    tree = json.loads(process.stdout)
    nodes = {}
    aliases = {}

    def visit(node):
        if "id" in node:
            nodes[node["id"]] = node
        if node.get("kind") == "TypedefDecl":
            aliases[node["name"]] = node
        for child in node.get("inner", []):
            visit(child)
    visit(tree)

    def record(node):
        for child in node.get("inner", []):
            if child.get("kind") == "RecordType":
                return nodes.get(child.get("decl", {}).get("id"))
            found = record(child)
            if found:
                return found
        return None

    def fields(node, prefix="", depth=0):
        if depth > 16:
            raise HarnessError("recursive output structure needs an explicit referent observer")
        if node.get("tagUsed") == "union":
            raise HarnessError("union output needs an explicit active-member observer")
        out = []
        inline_record = None
        for field in node.get("inner", []):
            if field.get("kind") == "RecordDecl":
                inline_record = field
                continue
            if field.get("kind") != "FieldDecl":
                continue
            name = field.get("name")
            ty = field["type"]["qualType"]
            if not name:
                if field.get("isImplicit") and inline_record:
                    out.extend(fields(inline_record, prefix, depth + 1))
                    continue
                raise HarnessError("unresolved anonymous output field")
            path = prefix + name
            array = re.fullmatch(r"(.+)\[(\d+)\]", ty)
            elements = [(path, ty)] if not array else [
                (f"{path}[{i}]", array[1]) for i in range(int(array[2]))]
            for path, ty in elements:
                if ty in SCALARS or field.get("isBitfield"):
                    out.append(path)
                elif ty in aliases and (nested := record(aliases[ty])):
                    out.extend(fields(nested, path + ".", depth + 1))
                elif inline_record and "(unnamed" in ty:
                    out.extend(fields(inline_record, path + ".", depth + 1))
                else:
                    raise HarnessError(f"output field {path}: {ty} needs an explicit observer")
        return out

    def resolve(ty):
        if ty not in aliases or not (node := record(aliases[ty])):
            raise HarnessError(f"no public output record found for {ty} in {header}")
        answer = fields(node)
        if not answer:
            raise HarnessError(f"empty output observation for {ty}")
        return answer
    return resolve


def observations(ty, var, field, resolve):
    """Returns initialization, observation code, and required semantic fields."""
    if ty in SCALARS:
        return f"{ty} {var} = ({ty})initial;", [
            f'df_u64("{field}", (uint64_t){var});'], [field]
    if ty == "uint8_t*":
        return f"uint8_t *{var} = buf;", [
            f'df_pointer("{field}", {var});'], [field]
    if ty == "OUT_T":
        init = (f"OUT_PAIR {var}_items[3] = {{{{0}}}}; "
                f"OUT_T {var} = {{ .current = {var}_items, .remainingCount = capacity }}; "
                f'df_region("{var}_items", {var}_items, sizeof {var}_items);')
        code = [f'df_pointer("{field}.current", {var}.current);',
                f'df_u64("{field}.remainingCount", {var}.remainingCount);']
        keys = [field + ".current", field + ".remainingCount"]
        for i in range(3):
            for member in ("f1", "f2"):
                key = f"{field}.items[{i}].{member}"
                code.append(f'df_u64("{key}", {var}_items[{i}].{member});')
                keys.append(key)
        return init, code, keys
    if ty == "VEC":
        init = (f"POINT_T {var}_items[3] = {{{{0}}}}; "
                f"VEC {var} = {{ .max = capacity, .cur = 0, .arr = {var}_items }}; "
                f'df_region("{var}_items", {var}_items, sizeof {var}_items);')
        code = [f'df_u64("{field}.max", {var}.max);',
                f'df_u64("{field}.cur", {var}.cur);',
                f'df_pointer("{field}.arr", {var}.arr);']
        keys = [field + ".max", field + ".cur", field + ".arr"]
        for i in range(3):
            for member in ("x", "y"):
                key = f"{field}.items[{i}].{member}"
                code.append(f'df_u64("{key}", {var}_items[{i}].{member});')
                keys.append(key)
        return init, code, keys
    if ty == "OPOINT":
        return f"OPOINT {var} = {{0}}; {var}.z = (uint32_t)initial;", [
            f'df_u64("{field}.x", {var}.x);',
            f'if ({var}.x == 0) df_u64("{field}.union", {var}.y); '
            f'else df_u64("{field}.union", {var}.z);'], [field + ".x", field + ".union"]
    fields = resolve(ty)
    init = f"{ty} {var} = {{0}}; " + " ".join(f"{var}.{p} = initial;" for p in fields)
    return init, [f'df_u64("{field}.{p}", (uint64_t){var}.{p});' for p in fields], [
        field + "." + p for p in fields]


def generate(module, left, right, includes, support="", extern=False, funptr=False,
             copy_setup=None, clang="clang"):
    """Generate wrappers AND direct calls, with exact old-style function pointers."""
    wrapper = left / (module + "Wrapper.h")
    public = left / (module + ".h")
    funcs = signatures(wrapper) if wrapper.exists() else {}
    other = signatures(right / wrapper.name) if wrapper.exists() else {}
    funcs.update(signatures(public, True))
    other.update(signatures(right / public.name, True))
    check_signatures(funcs, other)
    return emit(module, left, funcs, includes, support, extern, funptr, copy_setup, clang)


def emit(module, left, funcs, includes, support="", extern=False, funptr=False,
         copy_setup=None, clang="clang"):
    """Emit a driver after ABI validation; also usable for reference-only compiler checks."""
    wrapper = left / (module + "Wrapper.h")
    public = left / (module + ".h")
    if not funcs:
        raise HarnessError(f"{module}: no public callable functions")
    resolver = None

    def resolve(ty):
        nonlocal resolver
        if resolver is None:
            resolver = ast_fields(wrapper if wrapper.exists() else public, includes, clang)
        return resolver(ty)
    lines = [f'#include "{module}.h"']
    if wrapper.exists():
        lines.append(f'#include "{module}Wrapper.h"')
    if extern:
        lines.append("#define DF_EXTERN 1")
    lines += ['#include "observe.h"', support]
    lines += [f'void {module}EverParseError(const char *t, const char *f, const char *r) '
              '{ df_error_strings(t, f, r); ++df_errors; }']
    lines += [
        "static EVERPARSE_ERROR_HANDLER df_saved_handler;",
        "static void df_forward_error(const char *t, const char *f, const char *r,",
        " uint64_t c, uint8_t *ctx, EVERPARSE_INPUT_BUFFER input, uint64_t pos) {",
        " df_error(t, f, r, c, ctx, input, pos);",
        " df_saved_handler(t, f, r, c, ctx, input, pos);",
        "}",
    ]
    for fn, (ret, params) in funcs.items():
        if ret != "uint64_t" or "Validate" not in fn:
            continue
        decl = ", ".join(ty + " " + name for ty, name in params)
        names = [name for _, name in params]
        lines += [f"extern uint64_t __real_{fn}({decl});",
                  f"uint64_t __wrap_{fn}({decl}) {{"]
        handlers = [name for ty, name in params if ty == "EVERPARSE_ERROR_HANDLER"]
        contexts = [name for ty, name in params if ty == "uint8_t*" and name.lower() == "ctxt"]
        if handlers:
            handler = handlers[0]
            lines += [f"if ({handler} != df_error) {{",
                      f"df_saved_handler = {handler}; {handler} = df_forward_error;"]
            if contexts:
                lines.append(f'df_region("wrapper-context", {contexts[0]}, 0);')
            lines.append("}")
        lines += [f"uint64_t result = __real_{fn}({', '.join(names)});",
                  'df_u64("validator.return", result);',
                  'df_u64("validator.kind", result >> 60);',
                  'df_u64("validator.position", result & UINT64_C(0x0fffffffffffffff));',
                  "return result;", "}"]
    required = {}
    for index, (fn, (ret, params)) in enumerate(funcs.items()):
        types = ", ".join(ty for ty, _ in params) or "void"
        lines += [f"static {ret} (*const abi_{index})({types}) = &{fn};",
                  f"static void call_{index}(uint8_t *buf, uint32_t len, uint64_t arg, "
                  "uint64_t initial, uint64_t start, unsigned capacity, unsigned chunk) {"]
        args, post, keys = [], [], ["return", "error.count"]
        if ret in {"BOOLEAN", "uint64_t"}:
            keys += ["validator.return", "validator.kind", "validator.position"]
        direct = ret == "uint64_t" and "Validate" in fn
        input_index = (len(params) - 3 if direct else len(params) - 2) if not extern else -1
        if copy_setup:
            lines.append(f'df_prepare("{fn}", buf, len, arg);')
        if extern:
            lines += [
                f"struct es_cell cells[{MAX_INPUT}]; struct EVERPARSE_INPUT_STREAM_BASE_s stream = {{0}};",
                "unsigned count = 0; uint64_t off = 0;",
                "while (off < len) {",
                "  uint64_t n = len-off < chunk ? len-off : chunk;",
                "  cells[count].buf = buf+off; cells[count].len = n;",
                "  cells[count].next = NULL;",
                "  if (count) cells[count-1].next = &cells[count];",
                "  else stream.head = &cells[count];",
                "  ++count; off += n;",
                "}",
                'df_region("stream", &stream, sizeof stream);',
                "BOOLEAN stream_status = TRUE;",
                "EVERPARSE_EXTRA_T extra = " +
                ("makeExtraT(&stream_status);" if funptr else "0;"),
            ]
        lines += [f'df_region("input", buf, {MAX_INPUT});',
                  'uint8_t context[1] = {0}; df_region("context", context, sizeof context);']
        for parameter_index, (ty, name) in enumerate(params):
            key = "out." + name
            if name.lower() in {"ctxt", "context"}:
                args.append("context")
            elif ty == "EVERPARSE_ERROR_HANDLER":
                args.append("df_error")
            elif ty == "EVERPARSE_INPUT_BUFFER":
                args.append("(EVERPARSE_INPUT_BUFFER){.base=&stream, .has_length=(arg%2), "
                            ".length=start+len}")
            elif ty == "EVERPARSE_INPUT_STREAM_BASE":
                args.append("&stream")
            elif ty == "EVERPARSE_EXTRA_T":
                args.append("extra")
            elif parameter_index == input_index and ty == "uint8_t*":
                args.append("buf")
            elif not extern and parameter_index == input_index + 1 and (
                    (direct and ty == "uint64_t") or (ret == "BOOLEAN" and ty == "uint32_t")):
                args.append("len")
            elif direct and parameter_index == len(params) - 1 and ty == "uint64_t":
                args.append("start")
            elif ty == "EVERPARSE_COPY_BUFFER_T":
                if copy_setup is None:
                    raise HarnessError(f"{fn}: missing original-client copy-buffer observer")
                init, code, fields = copy_setup(fn, name, index)
                lines.append(init)
                args.append("&o_" + name)
                post.extend(code)
                keys.extend(fields)
            elif ty in SCALARS:
                value = "(arg & 1)" if ty in {"BOOLEAN", "bool"} else "arg"
                if (module, name.lower().strip("_")) in {
                        ("SpecializeTaggedUnionArray", "count"),
                        ("SpecializeVLArray", "unknownheadercount")}:
                    # Encode Count independently of the Requestor32 bit.
                    value = "arg >> 1"
                if module == "Specialize6":
                    semantic_name = name.lower().replace("_", "")
                    if semantic_name == "messagebodylength":
                        value = "64"
                    elif semantic_name == "apiversion":
                        value = "1 + arg%2"
                    elif semantic_name == "rawresponse":
                        value = "0"
                if name == "providedSize":
                    value = "arg == 255 ? 4096 : len"
                # Top-level probe addresses are logical source selections, not random pointers.
                if name == "probeAddr" and copy_setup:
                    value = "df_probe_address(arg)"
                args.append(f"({ty})({value})")
            elif ty.endswith("*"):
                init, code, fields = observations(ty[:-1], "o_" + name, key, resolve)
                lines.append(init)
                args.append("&o_" + name)
                post.extend(code)
                keys.extend(fields)
            else:
                raise HarnessError(f"{fn}: unhandled public type {ty}")
        lines += [f"{ret} result = abi_{index}({', '.join(args)});", *post]
        if extern:
            lines += ["uint64_t remaining = 0;",
                      "for (struct es_cell *p = stream.head; p; p = p->next) remaining += p->len;",
                      'df_u64("stream.remaining", remaining);',
                      'df_u64("stream.status", stream_status);']
            keys += ["stream.remaining", "stream.status"]
        if ret == "uint64_t" and direct:
            keys += ["return.kind", "return.position"]
        lines += [f'df_end(result, {int(ret == "uint64_t" and direct)});', "}"]
        required[fn] = {"fields": keys, "return": ret, "direct": direct}
        if module == "Probe" and fn in {
                "ProbeProbeInPlaceCheckTest1", "ProbeProbeInPlaceCheckTest2",
                "ProbeProbeInPlaceCheckTest3", "ProbeMyStruct", "ProbeBoth"}:
            required[fn]["negative_only"] = (
                "Original probe/src/main.c ProbeInPlace accepts exactly sizeof(secondary)=4; "
                "this wrapper requests 28, 42, or 3338 bytes. All outputs and rejection "
                "codes are still compared; success would be an unexpected outcome.")
    lines += ["int main(void) {",
              "unsigned fn, len, capacity, chunk; uint64_t arg, initial, start;",
              "int scanned;",
              f"char id[100], hex[{MAX_INPUT * 2 + 1}];",
              f'while ((scanned = scanf("%99s %u %u %" SCNu64 " %" SCNu64 " %" SCNu64 " %u %u %{MAX_INPUT * 2}s",',
              "             id, &fn, &len, &arg, &initial, &start, &capacity, &chunk, hex)) != EOF) {",
              '  if (scanned != 9) { fputs("malformed differential input\\n", stderr); return 2; }',
              f"  uint8_t buf[{MAX_INPUT}] = {{0}};",
              f"  if (len > {MAX_INPUT} || start > len || capacity > 3 || !chunk) return 2;",
              "  if (strcmp(hex, \"-\") && strlen(hex) != 2*len) return 2;",
              "  for (unsigned i=0; i<len; ++i) { unsigned v;",
              "    if (!isxdigit((unsigned char)hex[2*i]) || !isxdigit((unsigned char)hex[2*i+1])) return 2;",
              '    if (sscanf(hex+2*i, "%2x", &v) != 1) return 2; buf[i] = (uint8_t)v;',
              "  }",
              "  switch (fn) {"]
    for i, fn in enumerate(funcs):
        lines += [f'case {i}: df_begin(id, "{fn}");',
                  f"call_{i}(buf, len, arg, initial, start, capacity, chunk); break;"]
    lines += ["default: return 2;", "}", "}", "return ferror(stdin) ? 2 : 0;", "}"]
    return "\n".join(lines) + "\n", required
