module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnessesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

namespace GlobalTheory

theorem thetaValue_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S T _ _ _ _ φ y0 y hφ a n x P hP v0 w h0 h1
  obtain ⟨S', _, _, φ0, y0', F0, hff0, hm0, hv0, he0⟩ := h0
  obtain ⟨T', _, _, φ1, y1, F1, hff1, hm1, hv1, he1⟩ := h1

  have hm01 : FrMap (φ1.comp φ) y0 y1 := GlobalTheory.FramedBaseChange.trans φ φ1 hφ hm1

  let iS : Algebra S S' := φ0.toRingHom.toAlgebra
  let iT : Algebra S T' := (φ1.comp φ).toRingHom.toAlgebra
  have : Module.FaithfullyFlat S S' := hff0
  let iU : Algebra c.F (TensorProduct S T' S') :=
    ((algebraMap T' (TensorProduct S T' S')).comp (algebraMap c.F T')).toAlgebra
  have hsq : ∀ s : S, (1 : T') ⊗ₜ[S] φ0 s = (φ1 (φ s)) ⊗ₜ[S] (1 : S') := by
    intro s
    calc (1 : T') ⊗ₜ[S] φ0 s = (1 : T') ⊗ₜ[S] (s • (1 : S')) := by
          rw [← Algebra.algebraMap_eq_smul_one]; rfl
      _ = (s • (1 : T')) ⊗ₜ[S] (1 : S') := (TensorProduct.smul_tmul _ _ _).symm
      _ = (φ1 (φ s)) ⊗ₜ[S] (1 : S') := by
          rw [← Algebra.algebraMap_eq_smul_one]; rfl
  let ψ2 : T' →ₐ[c.F] TensorProduct S T' S' :=
    { algebraMap T' (TensorProduct S T' S') with commutes' := fun _ => rfl }
  let ψ1 : S' →ₐ[c.F] TensorProduct S T' S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] TensorProduct S T' S').toRingHom with
      commutes' := fun r => by
        show (1 : T') ⊗ₜ[S] algebraMap c.F S' r = algebraMap T' (TensorProduct S T' S') (algebraMap c.F T' r)
        rw [← φ0.commutes r, hsq, φ.commutes, φ1.commutes]
        rfl }
  have hcomp : ψ1.comp φ0 = ψ2.comp (φ1.comp φ) := by
    ext s
    exact hsq s
  have key := _root_.GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y0 a n x P hP S' φ0 y0' F0 T' (φ1.comp φ)
    y1 F1 hm0 hv0 hm01 hv1 (TensorProduct S T' S') ψ1 ψ2 hcomp
  rw [← he0, ← he1] at key
  have hv : ψ1 (φ0 v0) = ψ2 (φ1 (φ v0)) := congrArg (fun f => f v0) hcomp
  have hinj : Function.Injective (algebraMap T' (TensorProduct S T' S')) :=
    FaithfulSMul.algebraMap_injective T' (TensorProduct S T' S')
  exact hff1.injective (hinj (hv.symm.trans key))

end GlobalTheory
