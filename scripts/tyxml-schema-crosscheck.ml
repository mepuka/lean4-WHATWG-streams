(* Independent reading of a TyXML .mli through OCaml's own parser
   (compiler-libs): one line per type or value declaration,
   kind <TAB> line <TAB> module path <TAB> name, in source order. *)
let () =
  let file = Sys.argv.(1) in
  let ic = open_in_bin file in
  let lb = Lexing.from_channel ic in
  Location.init lb file;
  let sg = Parse.interface lb in
  let push path n = if path = "" then n else path ^ "." ^ n in
  let rec walk path items = List.iter (item path) items
  and item path (it : Parsetree.signature_item) =
    match it.psig_desc with
    | Psig_type (_, decls) ->
      List.iter (fun (d : Parsetree.type_declaration) ->
          Printf.printf "type\t%d\t%s\t%s\n" d.ptype_loc.loc_start.pos_lnum path d.ptype_name.txt) decls
    | Psig_value v ->
      Printf.printf "val\t%d\t%s\t%s\n" v.pval_loc.loc_start.pos_lnum path v.pval_name.txt
    | Psig_modtype { pmtd_name; pmtd_type = Some mt; _ } -> modtype (push path pmtd_name.txt) mt
    | Psig_module { pmd_name = { txt = Some n; _ }; pmd_type; _ } -> modtype (push path n) pmd_type
    | Psig_module { pmd_name = { txt = None; _ }; pmd_type; _ } -> modtype (push path "_") pmd_type
    | _ -> ()
  and modtype path (mt : Parsetree.module_type) =
    match mt.pmty_desc with
    | Pmty_signature items -> walk path items
    | Pmty_functor (_, body) -> modtype path body
    | _ -> ()
  in
  walk "" sg
