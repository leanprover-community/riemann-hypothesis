module

public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.UnramifiedExistence
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderScalars
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.Unramified
public import GroundTheory.LocalFields.MaximalUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

section Root

noncomputable def unramifiedRoot (n : ℕ+) : Ω :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  (exists_isPrimitiveRoot_card_pow_sub_one (K := F) (Ksep := Ω) n.ne_zero).choose

theorem isPrimitiveRoot_unramifiedRoot (n : ℕ+) :
    IsPrimitiveRoot (unramifiedRoot F Ω n) (Nat.card 𝓀[F] ^ (n : ℕ) - 1) :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  (exists_isPrimitiveRoot_card_pow_sub_one (K := F) (Ksep := Ω) n.ne_zero).choose_spec

noncomputable def unramifiedLevel (n : ℕ+) : IntermediateField F Ω :=
  F⟮unramifiedRoot F Ω n⟯

theorem unramifiedLevel_eq (n : ℕ+) : unramifiedLevel F Ω n = F⟮unramifiedRoot F Ω n⟯ :=
  rfl

theorem isUnramifiedSubextension_unramifiedLevel (n : ℕ+) :
    IsUnramifiedSubextension (unramifiedLevel F Ω n) :=
  (isUnramifiedSubextension_adjoin n.ne_zero (isPrimitiveRoot_unramifiedRoot F Ω n)).1

theorem finrank_unramifiedLevel (n : ℕ+) : Module.finrank F (unramifiedLevel F Ω n) = n :=
  (isUnramifiedSubextension_adjoin n.ne_zero (isPrimitiveRoot_unramifiedRoot F Ω n)).2

instance finiteDimensional_unramifiedLevel (n : ℕ+) :
    FiniteDimensional F (unramifiedLevel F Ω n) :=
  (isUnramifiedSubextension_unramifiedLevel F Ω n).1

instance isGalois_unramifiedLevel (n : ℕ+) : IsGalois F (unramifiedLevel F Ω n) :=
  IsUnramifiedSubextension.isGalois (isUnramifiedSubextension_unramifiedLevel F Ω n)

theorem unramifiedLevel_le {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    unramifiedLevel F Ω m ≤ unramifiedLevel F Ω n :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  IsUnramifiedSubextension.le_adjoin (isUnramifiedSubextension_unramifiedLevel F Ω m) n.ne_zero
    ((finrank_unramifiedLevel F Ω m).symm ▸ h) (isPrimitiveRoot_unramifiedRoot F Ω n)

end Root

section Structure

variable [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

instance isUnramified_unramifiedLevel (n : ℕ+) : IsUnramified F (unramifiedLevel F Ω n) :=
  ⟨IsUnramifiedSubextension.ramificationIndex_eq_one (isUnramifiedSubextension_unramifiedLevel F Ω n)⟩

noncomputable def unramifiedLevelInv (n : ℕ+) :
    groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2 →+ QZ :=
  (unramifiedInv F (unramifiedLevel F Ω n)).comp
    (h2GalUnitsAddEquiv F (unramifiedLevel F Ω n)).toAddMonoidHom

theorem unramifiedLevelInv_apply (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    unramifiedLevelInv F Ω n y =
      unramifiedInv F (unramifiedLevel F Ω n) (h2GalUnitsAddEquiv F (unramifiedLevel F Ω n) y) :=
  rfl

noncomputable def brauerInvFun (x : galoisBrauerGroup F Ω) : QZ :=
  open Classical in
  if h : ∃ (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2),
      (brauerInflation (unramifiedLevel F Ω n)).hom y = x then
    unramifiedLevelInv F Ω h.choose h.choose_spec.choose
  else 0

end Structure

end GroundTheory.ProfCoh
