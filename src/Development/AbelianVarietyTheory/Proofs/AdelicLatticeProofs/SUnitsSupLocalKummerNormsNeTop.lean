module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndexStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
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

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_sup_finNorm_ne_top : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → sUnits F S ⊔ finNorm p F δ S ≠ ⊤ := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hr htop
  obtain ⟨h0, h1⟩ := GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ S hp hζ hS hδ hr
  obtain ⟨-, h2⟩ := GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ
  have hle : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => (GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).2 F _ _ _
  have h3 : (finNorm p F δ S).index = (finNorm p F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h4 := Subgroup.relIndex_le_of_le_left hle h0
  have h5 := Nat.mul_le_mul_right ((kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S)) hp.two_le
  omega

end GlobalTheory.CNorm
