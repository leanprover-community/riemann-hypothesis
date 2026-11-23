module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def glTens (k : ℕ) : GL (Fin k) (AF F ⊗[F] E) ≃ₜ* GlobalTheory.CuspRep.GA E k where
  toMulEquiv := Units.mapEquiv (GlobalTheory.TateConv.tens F E).toRingEquiv.mapMatrix.toMulEquiv
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (GlobalTheory.TateConv.continuous_tens F E))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (GlobalTheory.TateConv.continuous_tens_symm F E))

theorem glTens_bc (k : ℕ) (γ : GL (Fin k) E) :
    glTens F E k (bc (inclR (F := F) (AF F)) γ) = GlobalTheory.CuspRep.ratGL E k γ := by
  ext i j
  change GlobalTheory.TateConv.tens F E ((1 : AF F) ⊗ₜ[F] (γ i j)) = algebraMap E _ (γ i j)
  rw [GlobalTheory.TateConv.tens, adeleTensorAlgEquivLeft_tmul, map_one, mul_one]

variable [_root_.NumberField.IsTotallyComplex E]

def cR (k : ℕ) (t : ℝ) : GL (Fin k) (AF F ⊗[F] E) := (glTens F E k).symm (GlobalTheory.UnitaryBC.splitCentre E k t)

def latR (k : ℕ) : Subgroup (GL (Fin k) (AF F ⊗[F] E)) :=
  (bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range ⊔ Subgroup.zpowers (cR F E k 1)

variable {F E}

theorem glTens_cR (k : ℕ) (t : ℝ) : glTens F E k (cR F E k t) = GlobalTheory.UnitaryBC.splitCentre E k t :=
  (glTens F E k).apply_symm_apply _

theorem continuous_cR (k : ℕ) : Continuous (cR F E k) :=
  (glTens F E k).symm.continuous.comp GlobalTheory.OneRep.SplitTwist.continuous_splitCentre

theorem cR_add (k : ℕ) (x y : ℝ) : cR F E k (x + y) = cR F E k x * cR F E k y := by
  rw [cR, cR, cR, splitCentre_add, map_mul]

theorem cR_comm (k : ℕ) (t : ℝ) (g : GL (Fin k) (AF F ⊗[F] E)) : cR F E k t * g = g * cR F E k t := by
  apply (glTens F E k).injective
  rw [map_mul, map_mul, glTens_cR, splitCentre_comm]

theorem latR_le (k : ℕ) : latR F E k ≤ (GlobalTheory.UnitaryBC.latticeGL E k).comap (glTens F E k).toMulEquiv.toMonoidHom := by
  refine sup_le ?_ ?_
  · rintro _ ⟨γ, rfl⟩
    show glTens F E k (bc (inclR (F := F) (AF F)) γ) ∈ GlobalTheory.UnitaryBC.latticeGL E k
    rw [glTens_bc]
    exact ratGL_mem_latticeGL γ
  · rw [Subgroup.zpowers_le]
    show glTens F E k (cR F E k 1) ∈ GlobalTheory.UnitaryBC.latticeGL E k
    rw [glTens_cR]
    simpa using zpow_mem_latticeGL (E := E) (a := k) 1

instance discreteTopology_latR (k : ℕ) : DiscreteTopology (latR F E k) :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : latR F E k => (⟨glTens F E k x.1, latR_le k x.2⟩ : GlobalTheory.UnitaryBC.latticeGL E k))
    (((glTens F E k).continuous.comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext ((glTens F E k).injective (congrArg Subtype.val h)))

end GlobalTheory.GLOneVol
