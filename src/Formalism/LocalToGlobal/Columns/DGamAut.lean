module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
public import Formalism.LocalToGlobal.Columns.CoefModAt
public import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
public import Formalism.LocalToGlobal.Columns.HeckeSpCount
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.Col

section One

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

variable {E n}

end One

section DGam

variable {X : Fields} {R : Ranks}

end DGam

section Stab

variable {X : Fields} {R : Ranks} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem dga_frm_stab_inj (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) {a b : FrmG Λ Θ}
    (ha : a • p = p) (hb : b • p = p) (hab : a.1 = b.1) : a = b := by
  have hda : ((a.1, (a.2.1 : GLG (E := X.E) (n := n) (SG := SG))) • p.deco : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) ha
  have hdb : ((b.1, (b.2.1 : GLG (E := X.E) (n := n) (SG := SG))) • p.deco : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) hb
  have h1 := DecoSet.stab_fst_injective p.deco hda hdb hab
  have h2 : (a.2.1 : GLG (E := X.E) (n := n) (SG := SG)) = b.2.1 := congrArg Prod.snd h1
  have h3 : ∀ P : Q, (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 := by
    intro P
    have ea : a.1.1 * p.fr P * (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) ha
    have eb : b.1.1 * p.fr P * (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) hb
    rw [← hab] at eb
    exact mul_left_cancel (ea.trans eb.symm)
  refine Prod.ext hab (Prod.ext (Subtype.ext h2) (Subtype.ext (funext fun P => ?_)))
  exact inv_injective (Subtype.ext (h3 P))

end Stab

end Formalism.L2.Col
