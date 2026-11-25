module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Mem.Col2.PtLat

theorem latS_deco_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q S k t y p ht hS hp x
  have hp0 : IsPtOf hc (y * (k * t)) (extTo ∅ p) :=
    hp.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)
  obtain ⟨hg, hd⟩ := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ _ _ rfl).1 hp0
  have hd' : p.deco.1 = decoRaw ST SG (y * (k * t)) := hd
  have hcar := decoRaw_carries hc n ST SG hg x
  rw [hd']
  refine hcar.trans ?_
  have hst := mirabolicLevel_le_stabilizer_base hc n ST (principal_le_congruence_subgroup hc n ST SG (Subgroup.inv_mem _ ht))
  have e : (((y * (k * t))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
      ((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  exact ((hst _).symm).trans (hS _).symm

end GlobalTheory.Mem.Col2.PtLat
