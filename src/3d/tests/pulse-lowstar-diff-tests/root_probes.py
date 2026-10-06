"""Wire-field observers for root grammars that have no original C probe client.

Offsets below describe the *serialized* aligned .3d layouts, not C structure
representations. Padding is deliberately not observed. Original subdirectory
probe clients are handled separately by clients.py, without these model hooks.
"""

from corpus import HarnessError
from driver import parameters
import re


def fields(module, name):
    key = name.lower().replace("_", "")
    a = [("a1", 0, 4, False), ("a2", 4, 4, False)]
    b = [("b1", 0, 4, False), ("pa", 8, 8, True),
         ("b2", 16, 4, False), ("b3", 20, 4, False)]
    c = [("c1", 0, 4, False), ("pb", 8, 8, True)]
    if module == "Specialize2":
        if key == "aout":
            return [("f.b0.b2", 0, 4, False), ("f.b0.b3", 4, 4, False)]
        if key == "aaout":
            return [("b2", 0, 8, True), ("b3", 8, 8, True)]
    if module in {"FineGrainedProbe", "Specialize3"}:
        return a if key == "aout" else b
    if module == "FineGrainedProbeSpecialize":
        return a if key == "aout" else c if key == "cout" else [
            ("b1", 0, 4, False), ("pa", 8, 8, True),
            ("b2.b1_1", 16, 4, False), ("b2.b1_2", 24, 8, True)]
    if module == "Specialize5":
        return [("Base", 0, 4, False), ("f1", 4, 2, False), ("f2", 6, 2, False),
                ("f3", 8, 2, False), ("ptr1", 16, 8, True), ("ptr2", 24, 8, True),
                ("ptr3", 32, 8, True), ("f4", 40, 2, False), ("f5", 42, 2, False)]
    if module == "Specialize6":
        if key == "out":
            return [("Response", 0, 8, True), ("Count", 8, 2, False), ("ptr1", 16, 8, True)]
        return [("f1", 0, 4, False), ("f2", 4, 4, False), ("f3", 8, 2, False),
                ("f4", 10, 2, False), ("ptr", 16, 8, True), ("Headers.f1", 24, 2, False),
                ("Headers.ptr", 32, 8, True),
                *[(f"Headers.pairs[{i}].f1", 40 + i * 16, 4, False) for i in range(30)],
                *[(f"Headers.pairs[{i}].f2", 48 + i * 16, 8, True) for i in range(30)],
                ("f5", 520, 2, False), ("ptr2", 528, 8, True)]
    raise HarnessError(f"unclassified root probe output: {module}/{name}")


MODEL = r"""
typedef struct { uint8_t bytes[1024]; uint64_t len; } df_copy;
static uint8_t df_memory[4096];
uint8_t *EverParseStreamOf(EVERPARSE_COPY_BUFFER_T p) { return ((df_copy*)p)->bytes; }
uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T p) { return ((df_copy*)p)->len; }
static uint64_t df_wire(const uint8_t *p, unsigned n) {
  uint64_t v=0; for(unsigned i=0;i<n;++i) v |= (uint64_t)p[i]<<(8*i); return v;
}
static void df_store(uint8_t *p, uint64_t v, unsigned n) {
  for(unsigned i=0;i<n;++i) p[i]=(uint8_t)(v>>(8*i));
}
static int df_address(uint64_t address, uint64_t off, uint64_t n) {
  return address >= 4096 && address-4096 <= sizeof df_memory &&
    off <= sizeof df_memory-(address-4096) &&
    n <= sizeof df_memory-(address-4096)-off;
}
static BOOLEAN df_copy_bytes(uint64_t n,uint64_t ro,uint64_t wo,uint64_t src,
                             EVERPARSE_COPY_BUFFER_T dst) {
  df_copy *p=dst;
  if (!df_address(src,ro,n) || wo>p->len || n>p->len-wo) return 0;
  memcpy(p->bytes+wo,df_memory+(src-4096)+ro,(size_t)n); return 1;
}
static uint64_t df_read(BOOLEAN *failed,uint64_t ro,uint64_t src,unsigned n) {
  if (!df_address(src,ro,n)) { *failed=1; return 0; }
  return df_wire(df_memory+src-4096+ro,n);
}
static BOOLEAN df_write(uint64_t v,uint64_t wo,EVERPARSE_COPY_BUFFER_T dst,unsigned n) {
  df_copy *p=dst; if(wo>p->len || n>p->len-wo) return 0;
  df_store(p->bytes+wo,v,n); return 1;
}
static void df_wire_pointer(const char *key,uint64_t value) {
  if(!value) { df_text(key,NULL); return; }
  if(df_address(value,0,0)) {
    char s[80]; snprintf(s,sizeof s,"probe-source+%" PRIu64,value-4096); df_text(key,s);
  } else { df_text(key,"<unregistered-pointer>"); }
}
static uint64_t df_probe_address(uint64_t arg) { return arg==255 ? 0 : 4096; }
"""


def support(module, out):
    header = out / (module + "_ExternalAPI.h")
    if not header.exists():
        raise HarnessError(f"{module}: missing generated external API")
    text = header.read_text()
    code = MODEL + f'\n#include "{header.name}"\n'
    for ret, fn, raw in re.findall(
            r"extern\s+(BOOLEAN|uint\d+_t)\s+(\w+)\s*\(([^;]+)\);", text, re.S):
        params = parameters(raw)
        names = [p[1] for p in params]
        decl = ", ".join(ty + " " + name for ty, name in params)
        if fn.startswith("ProbeAndCopy"):
            body = "return df_copy_bytes(" + ",".join(names) + ");"
        elif re.match(r"(ProbeAndReadU|ReadU)\d+", fn):
            width = int(re.search(r"U(16|32|64)", fn)[1]) // 8
            body = f"return ({ret})df_read({','.join(names[:3])},{width});"
        elif re.match(r"(WriteU|ProbeAndWriteU)\d+", fn):
            width = int(re.search(r"U(16|32|64)", fn)[1]) // 8
            body = f"return df_write({','.join(names)},{width});"
        elif fn.startswith("ProbeInit"):
            body = f"return {names[1]} <= ((df_copy*){names[2]})->len;"
        elif fn.startswith("UlongToPtr"):
            body = f"return {names[0]};"
        else:
            raise HarnessError(f"unknown root probe callback: {fn}")
        code += f"{ret} {fn}({decl}) {{ {body} }}\n"
    code += """
static void df_prepare(const char *fn,uint8_t *buf,uint32_t len,uint64_t arg) {
  (void)fn; memset(df_memory,0,sizeof df_memory);
  df_store(df_memory+264,4608,8);
  df_store(df_memory+256,0,4);
  df_store(df_memory+512,17,4); df_store(df_memory+516,18,4);
"""
    if module == "Specialize2":
        code += """
  if(len>=32) { memset(buf,0,len);
    df_store(buf+(arg&1 ? 4:8),4608,arg&1 ? 4:8);
    df_store(buf+(arg&1 ? 16:24),4864,arg&1 ? 4:8); }
"""
    elif module == "FineGrainedProbe":
        code += """
  df_store(df_memory+260,4608,4);
  if(len>=8) { memset(buf,0,len); df_store(buf+4,4352,4); }
"""
    elif module == "Specialize3":
        code += """
  if(arg&1) df_store(df_memory+260,4608,4);
  if(len>=16) { memset(buf,0,len); df_store(buf+(arg&1 ? 4:8),4352,arg&1 ? 4:8); }
"""
    elif module == "FineGrainedProbeSpecialize":
        code += """
  df_store(df_memory+(arg&1 ? 4:8),4352,arg&1 ? 4:8);
  if(arg&1) df_store(df_memory+260,4608,4);
  if(len>=8) { memset(buf,0,len); df_store(buf,4096,arg&1 ? 4:8); }
"""
    elif module == "Specialize6":
        code += """
  df_store(df_memory,5120,8);
  if(len>=8) { memset(buf,0,len); df_store(buf,4096,arg&1 ? 4:8); }
"""
    else:
        code += """
  if(len>=8) { memset(buf,0,len); df_store(buf,4096,arg&1 ? 4:8); }
"""
    code += "}\n"

    def setup(fn, name, index):
        var = "o_" + name
        semantic_fields = fields(module, name)
        init = (f"df_copy {var} = {{.len=capacity ? 1024 : 0}}; "
                f"memset({var}.bytes,0,sizeof {var}.bytes); "
                f'df_region("{name}.storage",{var}.bytes,sizeof {var}.bytes);')
        obs, keys = [], []
        for field, offset, size, pointer in semantic_fields:
            key = f"out.{name}.{field}"
            value = f"df_wire({var}.bytes+{offset},{size})"
            obs.append(f'{"df_wire_pointer" if pointer else "df_u64"}("{key}",{value});')
            keys.append(key)
        if module == "Specialize6" and name.lower().replace("_", "") != "out":
            for field, off, size, ptr in [("RESP2.f2", 536, 2, False), ("RESP2.ptr", 544, 8, True)]:
                obs.append(f'if(arg%2 == 0) {"df_wire_pointer" if ptr else "df_u64"}'
                           f'("out.{name}.{field}",df_wire({var}.bytes+{off},{size}));')
        return init, obs, keys
    return code, setup
