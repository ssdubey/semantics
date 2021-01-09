type content = Node | Content

type branch = Branch of string

(*for keys*)
type hash =
  | Hash_block of string
  | Hash_tree of (content * string * hash) list
  | Hash_commit of (hash list * hash)
  | Hash_dummy

(*for values*)
type commit = Commit of (hash list * hash)

type tree = Tree of (content * string * hash) list

type block = Block of string

type value =
  | Value_commit of commit
  | Value_tree of tree
  | Value_block of block

module Tag_module = struct
  type t = branch

  let compare t1 t2 =
    match (t1, t2) with Branch b1, Branch b2 -> String.compare b1 b2
end

module TagMap = Map.Make (Tag_module)

module Block_module = struct
  type t = hash

  let compare t1 t2 = compare t1 t2
end

module BlockMap = Map.Make (Block_module)