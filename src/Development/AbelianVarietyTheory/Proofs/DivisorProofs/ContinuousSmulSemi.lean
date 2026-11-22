module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

@[expose] public section

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.DiffDecay

section Weak

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def WithSemi (_p : Seminorm ℂ E) : Type := E

instance (p : Seminorm ℂ E) : AddCommGroup (WithSemi p) := inferInstanceAs (AddCommGroup E)
instance (p : Seminorm ℂ E) : Module ℂ (WithSemi p) := inferInstanceAs (Module ℂ E)
instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithSemi p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := WithSemi p) p.toAddGroupSeminorm
instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithSemi p) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le

end Weak

section Tame

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]

end Tame

section Heis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]

end Heis

end GlobalTheory.DiffDecay

end
