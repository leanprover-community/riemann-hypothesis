module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaSection
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.USelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsV :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y), ∃ v : Fin d → Γ(TP B j, ⊤), IsV B j v ∧ Ideal.span (Set.range v) = ⊤ := by
  intro K _ W Z Y q i π D d B T j
  classical
  let X : B.ι × Fin d → Scheme.{0} := fun p => (oT B j p : Scheme.{0})
  choose v hv _ using fun m : Fin d =>
    sigmaSection X (fun p => uV B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) m)
  refine ⟨v, fun p m => hv m p, ?_⟩
  choose b hb _ using fun m : Fin d =>
    sigmaSection X (fun p => if p.2 = m then (1 : Γ(X p, ⊤)) else 0)
  obtain ⟨s, -, hs⟩ := sigmaSection X (fun _ => 1)
  have h1 : (∑ m, b m * v m) = 1 := by
    have e2 := hs 1 (fun p => map_one _)
    have e1 : (∑ m, b m * v m) = s := by
      refine hs _ fun p => ?_

      rw [map_sum]
      simp only [map_mul, hb, hv]
      simp [uSelf]
    rw [e1, e2]
  rw [Ideal.eq_top_iff_one, ← h1]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
