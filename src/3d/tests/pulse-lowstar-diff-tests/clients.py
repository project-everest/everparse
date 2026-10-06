"""Adapters around unchanged corpus clients (included, not rewritten)."""

def include_client(path, module):
    return (f"#define main df_original_main\n"
            f"#define {module}EverParseError df_original_error\n"
            f'#include "{path.as_posix()}"\n'
            f"#undef {module}EverParseError\n#undef main\n")


def support_for(suite, module, source, generated=None):
    support, extra, setup = "", [], None
    if suite == "root" and module in {
            "FineGrainedProbe", "FineGrainedProbeSpecialize",
            "Specialize2", "Specialize3", "Specialize5", "Specialize6"}:
        from root_probes import support as root_support
        support, setup = root_support(module, generated)
    elif suite in {"extern", "static", "funptr"}:
        extra = [source / "src/EverParseStream.c"]
        if suite == "funptr":
            support = include_client(source / "src/main.c", module)
    elif suite == "tcpip":
        extra = [source / "extern/EverParseStream.c"]
    elif suite.startswith("iter/"):
        extra = [source / "src/Test_ExternalTypedefs.c"]
    elif module == "ExternVector":
        support = include_client(source / "ExternVectorDriver.c", module)
    elif suite in {"probe", "probe_error_handler_macro", "specialize_test",
                    "specialize_test_error_handler_macro", "specialize_test2",
                    "specialize_tagged_union_array"}:
        support = include_client(source / "src/main.c", module)
        if suite.startswith("probe"):
            support += """
static uint64_t df_probe_address(uint64_t arg) {
  return arg == 255 ? 0 : (uint64_t)(uintptr_t)secondary;
}
static void df_prepare(const char *fn, uint8_t *buf, uint32_t len, uint64_t arg) {
  (void)fn;
  df_region("secondary", secondary, sizeof secondary);
  if (len >= 16) {
    uint64_t addr = df_probe_address(arg), bound = arg % 3;
    memcpy(buf, &bound, 8); memcpy(buf+8, &addr, 8);
  }
}
"""

            def setup(fn, name, index):
                var = "o_" + name
                # A byte array is a wire buffer, not a C object representation.
                init = (f"uint8_t {var}_bytes[8]; memset({var}_bytes, (uint8_t)initial, 8); "
                        f"copy_buffer_t {var} = {{ .buf={var}_bytes, .len=capacity ? 8 : 0 }}; "
                        f'df_region("{name}.storage", {var}_bytes, 8);')
                code = [f'df_pointer("out.{name}.buffer", {var}.buf);',
                        f'df_u64("out.{name}.length", {var}.len);',
                        f"for (unsigned j=0; j<{var}.len; ++j) {{ char key[100]; "
                        f'snprintf(key, sizeof key, "out.{name}.byte[%u]", j); '
                        f"df_u64(key, {var}.buf[j]); }}"]
                return init, code, [f"out.{name}.buffer", f"out.{name}.length"]
        elif suite in {"specialize_test", "specialize_test_error_handler_macro"}:
            support += """
static uint64_t df_probe_address(uint64_t arg) { return arg % 7; }
static void df_prepare(const char *fn, uint8_t *buf, uint32_t len, uint64_t arg) {
  (void)fn;
  if (len >= 8) { uint64_t addr = arg % 7; memcpy(buf, &addr, 8); }
}
"""

            def setup(fn, name, index):
                is_a = name.lower().replace("_", "") in {"aout"}
                ty = "A" if is_a else "B64"
                fields = ["a1", "a2"] if is_a else [
                    "b1", "pa", *[f"ps[{i}].{p}" for i in range(4) for p in ("p1", "p2")]]
                var = "o_" + name
                init = (f"{ty} {var}_data = {{0}}; " +
                        " ".join(f"{var}_data.{f} = initial;" for f in fields) +
                        f" copy_buffer_t {var} = {{ .buf=(uint8_t*)&{var}_data, "
                        f".len=capacity ? sizeof {var}_data : 0, "
                        f".type={'COPY_BUFFER_A' if is_a else 'COPY_BUFFER_B'} }}; "
                        f'df_region("{name}.storage",&{var}_data,sizeof {var}_data);')
                code = [f'df_u64("out.{name}.{f}", {var}_data.{f});' for f in fields]
                return init, code, [f"out.{name}.{f}" for f in fields]
        else:
            tagged = suite == "specialize_tagged_union_array"
            array64 = "w64_array" if tagged else "uh64"
            array32 = "w32_array" if tagged else "uh32"
            support += f"""
static uint64_t df_probe_address(uint64_t arg) {{
  return arg == 255 ? 0 : (uint64_t)(uintptr_t)(arg & 1 ? {array32} : {array64});
}}
static void df_prepare(const char *fn, uint8_t *buf, uint32_t len, uint64_t arg) {{
  (void)fn;
  df_region("source64", {array64}, sizeof {array64});
  df_region("source32", {array32}, sizeof {array32});
  if (len >= 8) {{ uint64_t addr = df_probe_address(arg); memcpy(buf, &addr, 8); }}
}}
"""

            def setup(fn, name, index):
                var = "o_" + name
                ty = "WRAPPER_64" if tagged else "UH64"
                init = (f"{ty} {var}_data[4] = {{{{0}}}}; "
                        f"copy_buffer_t {var} = {{.buf=(uint8_t*){var}_data, "
                        f".len=capacity ? sizeof {var}_data : 0 }}; "
                        f'df_region("{name}.storage",{var}_data,sizeof {var}_data);')
                code, keys = [], []
                for i in range(4):
                    base = f"{var}_data[{i}]"
                    key = f"out.{name}[{i}]"
                    if tagged:
                        code += [f'df_u64("{key}.Tag", {base}.Tag);',
                                 f'if ({base}.Tag == 0) {{ df_u64("{key}.payload.f0", {base}.payload.p0.f0);'
                                 f' df_u64("{key}.payload.ptr", {base}.payload.p0.ptr); }} '
                                 f'else df_u64("{key}.payload.ptr", {base}.payload.p.ptr1);']
                        keys += [key + ".Tag", key + ".payload.ptr"]
                    else:
                        for field in ("NameLength", "RawValueLength", "pName", "pRawValue"):
                            code.append(f'df_u64("{key}.{field}", {base}.{field});')
                            keys.append(key + "." + field)
                return init, code, keys
    return support, extra, setup
