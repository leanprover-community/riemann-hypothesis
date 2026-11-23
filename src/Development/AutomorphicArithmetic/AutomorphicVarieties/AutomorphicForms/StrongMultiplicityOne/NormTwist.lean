module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.normTwist :
    UpperTheory.V.Af.StrongMultiplicityOne.NormTwist := by
  intro E _ _ _ n hn π
  obtain ⟨κ, hκ⟩ := GlobalTheory.CuspRep.Central.exists_hasCentral E n π
  let z : {r : ℝ // 0 < r} →* (Ad E)ˣ :=
    (Reduction.posIdeleHom E).comp (Reduction.rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹)
  have hz : ∀ s, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) (z s) := fun s => Units.ext rfl
  have hc : Continuous z := Reduction.continuous_posIdeleHom.comp (Reduction.continuous_rpowHom _)
  have hm : ∀ s, GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n) = s := fun s => by
    have h := Reduction.detModule_centralSection (K := E) hn s
    rw [hz] at h
    refine Eq.trans (congrArg _ (Units.ext ?_)) h
    change _ = Matrix.det (Matrix.diagonal fun _ : Fin n => (z s).val)
    simp
  let ν : Formalism.L2.Host.HChar E := ⟨(κ⁻¹.1.comp z).comp (GroundTheory.Global.IdeleGroup.ideleModule E),
    (κ⁻¹.2.1.comp hc).comp GroundTheory.Global.IdeleGroup.continuous_ideleModule, fun k => by
      have h := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (K := E) k
      exact (congrArg (κ⁻¹.1.comp z) h).trans (map_one _)⟩
  refine ⟨ν, fun φ hφ s g => ?_⟩
  rw [hz, (hκ.twist ν).apply hφ]
  have e : (κ * ν ^ n).1 (z s) = 1 := by
    change κ.1 (z s) * (ν.1 ^ n) (z s) = 1
    rw [MonoidHom.pow_apply, ← map_pow]
    change κ.1 (z s) * (κ.1 (z (GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n))))⁻¹ = 1
    rw [hm, mul_inv_cancel]
  rw [e]
  simp
