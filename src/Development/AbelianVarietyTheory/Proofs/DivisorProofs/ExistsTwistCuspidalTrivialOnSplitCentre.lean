module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GKNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_splitCentre_eigen (π : CuspSub E a) : ∃ c : ℂ, ∀ φ ∈ π.V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π (1 : Cinf E)
  refine ⟨c, fun φ hφ t g => ?_⟩
  have e3 : GlobalTheory.CuspRep.Central.scL a (fun _ : InfinitePlace E => (t : ℂ)) =
      t • GlobalTheory.CuspRep.Central.scL (E := E) a 1 := by
    ext i j w
    by_cases hij : i = j <;> simp [hij]
  have h1 := GlobalTheory.CuspRep.Central.rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) φ (by
    rw [e3, map_smul, LinearMap.smul_apply, hc φ hφ, mul_comm, mul_smul, Complex.coe_smul])
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  exact congrFun (congrArg Subtype.val h1) g

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  intro E _ _ _ a ha π
  obtain ⟨c, hs⟩ := exists_splitCentre_eigen π
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) (a := a) (by omega) (-c)
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩ t g
  change (mulChi a χ φ).1 _ = (mulChi a χ φ).1 _
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hs φ hφ, mul_mul_mul_comm, ← Complex.exp_add]
  simp

end GlobalTheory.GKNorm

end
