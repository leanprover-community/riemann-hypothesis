module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison.Pb

namespace CrystallineSemistableComparison.Om.Glob

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def formCos {ι : Type} (U : ι → X.Opens) (a : ℕ) : Cos.{0} K where
  X n := ∀ i : Fin (n + 1) → ι, OmU q (capO U i) a
  δ n k := LinearMap.pi fun i => (formRes q (capO_comp U i k.succAbove) a).comp (LinearMap.proj (i ∘ k.succAbove))
  rel n j i x := by
    funext t
    have e : (t ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove = (t ∘ j.succAbove) ∘ i.succAbove :=
      funext fun k => congrArg t (Fin.succAbove_succAbove_succAbove_predAbove j i k)
    have key : ∀ (b b' : Fin (n + 1) → ι) (hb : b = b') (h : capO U t ≤ capO U b) (h' : capO U t ≤ capO U b'),
        formRes q h a (x b) = formRes q h' a (x b') := by
      intro b b' hb h h'
      subst hb
      rfl
    change formRes q _ a (formRes q _ a (x _)) = formRes q _ a (formRes q _ a (x _))
    rw [formRes_formRes, formRes_formRes]
    exact key _ _ e _ _

abbrev KC (U : Cov q) (a : ℕ) : ObjectProperty (Thick (smFun X q)) := KS q (a + 1) (Set.range U.U)

abbrev Fk (U : Cov q) (a : ℕ) : (KC q U a).FullSubcategory ⥤ ModuleCat.{0} K := (KC q U a).ι ⋙ HT.grT (smFun X q) a

def Vk (U : Cov q) (a : ℕ) (α : U.ι) : ObjectProperty (KC q U a).FullSubcategory :=
  fun T => InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U.U α) T.obj

end

end CrystallineSemistableComparison.Om.Glob
