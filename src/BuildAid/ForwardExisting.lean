macro "atlas_forward_decl " t:ident : tactic =>
  `(tactic| first | exact @$t | exact $t | (intros; apply $t <;> assumption))
