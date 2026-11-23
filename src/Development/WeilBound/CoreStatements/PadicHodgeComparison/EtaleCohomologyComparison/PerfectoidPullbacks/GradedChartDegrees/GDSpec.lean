module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]

structure OL : Prop where
  tf : R.TF (S := O)
  unit : ∀ u : ℕ, ¬ l ∣ u → IsUnit (u : O)

variable {l O}

abbrev Om (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : Type := O ⧸ Ideal.span {(l : O) ^ m}

abbrev Iom (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : Ideal (Om l O m) := (Ideal.span {(l : O)}).map (Ideal.Quotient.mk _)

def pdm (h : OL l O) (m : ℕ) : DividedPowers (Iom l O m) := (exists_pd_l l h.unit h.tf m).choose

theorem isPdm (h : OL l O) (m : ℕ) : R.IsPd (Ideal.Quotient.mk _) (Ideal.span {(l : O)}) (pdm h m) :=
  (exists_pd_l l h.unit h.tf m).choose_spec

abbrev κm (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : O →+* Om l O m ⧸ Iom l O m :=
  (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _)

abbrev Lm (h : OL l O) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) : (nlBase (Om l O m) (Iom l O m) (pdm h m) l).Fun :=
  nlFun (pdm h m) l X q (κm l O m)

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

abbrev lm (T : Thick (smFun X q)) (m : ℕ) : Ideal T.B := Ideal.span {(l : T.B) ^ m}

abbrev GI (T : Thick (smFun X q)) : Ideal T.B := T.J ⊔ Ideal.span {(l : T.B)}

abbrev GB (T : Thick (smFun X q)) (m : ℕ) : Type := T.B ⧸ lm (l := l) T m

abbrev GJ (T : Thick (smFun X q)) (m : ℕ) : Ideal (GB (l := l) T m) := (GI (l := l) T).map (Ideal.Quotient.mk _)

theorem lm_le (T : Thick (smFun X q)) (m : ℕ) : Ideal.span {(l : O) ^ m} ≤ (lm (l := l) T m).comap T.i := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change T.i ((l : O) ^ m) ∈ lm (l := l) T m
  rw [map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

def iG (T : Thick (smFun X q)) (m : ℕ) : Om l O m →+* GB (l := l) T m := Ideal.quotientMap _ T.i (lm_le T m)

def thG (T : Thick (smFun X q)) (m : ℕ) : T.B ⧸ T.J →+* GB (l := l) T m ⧸ GJ (l := l) T m :=
  Ideal.quotientMap _ (Ideal.Quotient.mk _) fun _ hx => Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hx)

def Good (T : Thick (smFun X q)) (m : ℕ) : Prop :=
  R.TF (S := T.B) ∧ R.PdI (GI (l := l) T) ∧
    ∀ x ∈ GI (l := l) T, x ∈ lm (l := l) T m → ∀ j : ℕ, j ≠ 0 → ∀ y : T.B, (j.factorial : T.B) * y = x ^ j → y ∈ lm (l := l) T m

def GD (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) : DividedPowers (GJ (l := l) T m) :=
  (RL.pd_quot hT.1 (GI (l := l) T) (lm (l := l) T m) hT.2.1 hT.2.2).choose

theorem GD_spec (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    R.IsPd (Ideal.Quotient.mk (lm (l := l) T m)) (GI (l := l) T) (GD T m hT) :=
  (RL.pd_quot hT.1 (GI (l := l) T) (lm (l := l) T m) hT.2.1 hT.2.2).choose_spec

end CrystallineSemistableComparison.Pb.Diso
