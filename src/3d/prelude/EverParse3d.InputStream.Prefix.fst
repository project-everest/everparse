module EverParse3d.InputStream.Prefix

noeq
type t (b: Type0) = {
  base: b;
  new_len_all: U32.t;
}

module I = EverParse3d.InputStream

let inst #base #base_inst = {
    live = begin fun x h ->
      I.live x.base h /\
      Seq.length (I.get_read x.base h) <= U32.v x.new_len_all /\
      U32.v x.new_len_all <= I.length_all #_ #base_inst x.base
    end;

    footprint = begin fun x ->
      I.footprint x.base
    end;

    live_not_unused_in = begin fun x h ->
      I.live_not_unused_in x.base h
    end;

    len_all = begin fun x ->
      x.new_len_all
    end;

    get_all = begin fun x ->
      if U32.v x.new_len_all <= I.length_all #_ #base_inst x.base
      then Seq.slice (I.get_all x.base) 0 (U32.v x.new_len_all)
      else (* dummy *) Seq.create (U32.v x.new_len_all) 0uy
    end;

    get_remaining = begin fun x h ->
      Seq.slice (I.get_all x.base) (Seq.length (I.get_read x.base h)) (U32.v x.new_len_all)
    end;

    get_read = begin fun x h ->
      I.get_read x.base h
    end;

    preserved = begin fun x l h h' ->
      I.preserved x.base l h h'
    end;

    has = begin fun x n ->
      let currentPosition = I.get_read_count x.base in
      let remainingLength = x.new_len_all `U32.sub` currentPosition in
      n `U32.lte` remainingLength
    end;

    read = begin fun x n dst ->
      I.read x.base n dst
    end;

    skip = begin fun x n ->
      I.skip x.base n
    end;

    get_read_count = begin fun x ->
      I.get_read_count x.base
    end;

}

let made_from #_ #base_inst x from =
  x.base == from

let get_suffix #_ #base_inst x =
  if U32.v x.new_len_all <= I.length_all #_ #base_inst x.base
  then Seq.slice (I.get_all x.base) (U32.v x.new_len_all) (I.length_all #_ #base_inst x.base)
  else (* dummy *) Seq.empty

let made_from_prop
  x from h
=
  ()

let make
  from n
=
  let currentPosition = get_read_count from in
  {
    base = from;
    new_len_all = currentPosition `U32.add` n;
  }
