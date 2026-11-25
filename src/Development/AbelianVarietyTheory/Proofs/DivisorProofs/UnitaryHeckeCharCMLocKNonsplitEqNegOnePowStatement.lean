module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  first | exact @GlobalTheory.BCT.inertChar_muLocK
