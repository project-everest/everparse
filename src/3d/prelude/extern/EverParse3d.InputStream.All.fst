module EverParse3d.InputStream.All

open EverParse3d.InputStream.Extern

let t = t

let inst = {
  live = live;
  footprint = footprint;
  live_not_unused_in = live_not_unused_in;
  len_all = len_all;
  get_all = get_all;
  get_remaining = get_remaining;
  get_read = get_read;
  preserved = preserved;
  has = has;
  read = read;
  skip = skip;
  empty = empty;
  is_prefix_of = is_prefix_of;
  get_suffix = get_suffix;
  is_prefix_of_prop = is_prefix_of_prop;
  truncate = truncate;
}
