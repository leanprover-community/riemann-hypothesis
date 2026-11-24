module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesC
public import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesD

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def LocalSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (j : Fin A.n) (χ w : X → ℝ), A.Smooth χ → A.Smooth w →
    tsupport χ ⊆ (A.chart j).source → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) χ = mInt A (Fin.cons (LocPot.ofFun χ) Φ) w

theorem localSymm : LocalSymmStatement := by
  intro e X _ _ _ A _ χ w hχ hw _ Φ hΦ
  exact st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm A χ w hχ hw Φ hΦ

theorem stokes : StokesStatement := st_stokes_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsSymm : ByPartsSymmStatement := st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsNonpos : ByPartsNonposStatement :=
  st_byPartsNonpos_of ReciprocityTheory.AnForm.A.parts_thm ReciprocityTheory.AnForm.A.gradDensNonneg_thm
theorem massIndep : MassIndepStatement := st_massIndep_of ReciprocityTheory.AnForm.A.parts_thm

end

end ReciprocityTheory.AnForm.M
