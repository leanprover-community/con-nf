import Mathlib.Data.ByteArray
import Lean
import ConNF

open Lean

/-- Extracts the names of the declarations in `env` on which `decl` depends. -/
-- source:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Counting.20prerequisites.20of.20a.20theorem/near/425370265
def getVisited (env : Environment) (decl : Name) :=
  let (_, { visited, .. }) := Elab.Command.CollectAxioms.collect decl |>.run env |>.run {}
  visited

def nameCode (n : Name) : String :=
  if n = .anonymous then
    "anonymous"
  else
    n.toString.replace "." "_"

def nameDisplay (n : Name) : String :=
  n.components.getLast!.toString

def printDeps₁ (k : Name) (v : Array Name) (print : String → IO Unit) : IO Unit := do
  let n := k.componentsRev[1]!
  print (nameCode k ++ " [label=\"" ++ nameDisplay k ++ "\"" ++ " group=\"" ++ n.toString ++ "\"]" ++ ";\n")

def printDeps₂ (k : Name) (v : Array Name) (print : String → IO Unit) : IO Unit := do
  for val in v do
    if (`ConNF).isPrefixOf val then
      print (nameCode val ++ " -> " ++ nameCode k ++ ";\n")

def group (name : Name) : Name :=
  (name.eraseSuffix? name.componentsRev.head!).get!

def groups (imports : NameMap (Array Name)) : NameMap Unit :=
  RBMap.fromList (imports.fold (fun xs k _ =>
    if (`ConNF).isPrefixOf k then (group k, ()) :: xs else xs) []) _

/-- `#deptree` outputs a graphviz dependency graph to `depgraph.dot`. Build it with
`dot -Tpdf -Gnewrank=true -Goverlaps=false -Gsplines=ortho depgraph.dot > depgraph.pdf`. -/
elab "#deptree " : command => do
  let env ← getEnv
  let imports := env.importGraph
  IO.FS.withFile "depgraph.dot" IO.FS.Mode.write fun h => do
  h.write "digraph {\n".toAsciiByteArray
  h.write "compound=true;\n".toAsciiByteArray
  for (gp, _) in groups imports do
    h.write ("subgraph cluster_" ++ nameCode gp ++ " {\n").toAsciiByteArray
    for (k, v) in imports do
      if (`ConNF).isPrefixOf k && group k = gp then do
        printDeps₁ k v (fun s => h.write s.toAsciiByteArray)
    h.write ("label = \"" ++ gp.toString ++ "\";\n").toAsciiByteArray
    h.write ("margin = 32;\n").toAsciiByteArray
    h.write ("pad = 32;\n").toAsciiByteArray
    h.write ("penwidth = 5;\n").toAsciiByteArray
    h.write ("color = cyan4;\n").toAsciiByteArray
    h.write "}\n".toAsciiByteArray
  for (k, v) in imports do
    if (`ConNF).isPrefixOf k then do
      printDeps₂ k v (fun s => h.write s.toAsciiByteArray)
  h.write "}\n".toAsciiByteArray

#deptree
