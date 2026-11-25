module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]


open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.finKs (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.Ks K s) := by
  classical
  have hl : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hK : FiniteDimensional ℚ_[l] ↥(K.1) := K.2
  have hK0 : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : (K.1 : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) ⊓
        _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l ≤ K.1)).toLinearMap (RingHom.injective _)
  have hfin : {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}.Finite := by
    refine (Polynomial.nthRoots (l ^ s) (1 : _root_.Formalism.BasicNotions.Loc.Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hl] using hx
  have : Finite {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1} := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hl (by rw [show x ^ l ^ s = 1 from hx]; exact isIntegral_one)
  unfold _root_.Formalism.BasicNotions.Loc.Ks
  infer_instance

def levelField (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finKs K s⟩

section Generic

variable {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]

def charLat (hO : Function.Injective (algebraMap O LL)) (ψ : G →* LLˣ)
    (hψ : ∀ g, ∃ a : O, algebraMap O LL a = ((ψ g : LLˣ) : LL)) :
    Lattice (O := O) (charRep ψ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hψ g
    refine ⟨b * a, ?_⟩
    change algebraMap O LL (b * a) = ((ψ g : LLˣ) : LL) * algebraMap O LL a
    rw [map_mul, hb]
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hO)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

variable [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) [Algebra Qp LL] [TopologicalSpace LL]
    [ContinuousAdd LL] [ContinuousConstSMul LL LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))

end Generic


open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem (P : _root_.Formalism.BasicNotions.LocPrime l) (K LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (g : ↥(_root_.Formalism.BasicNotions.Loc.GK K)) :
    ((_root_.Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : _root_.Formalism.BasicNotions.Loc.GQ l) 0 1 (by simp)
  have hnorm : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have ha' : ‖(a : ℚ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] a
    calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
        = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) + a‖ := by ring_nf
      _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le (by simpa using ha) ha'
  unfold _root_.Formalism.MainNotions.N.cycLL
  show algebraMap ℚ_[l] LL (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∈ _
  rw [P.PD_χ K g]
  have hmap : algebraMap ℚ_[l] LL ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) =
      algebraMap ℤ_[l] LL ⟨_, hnorm⟩ := rfl
  rw [hmap]
  unfold _root_.Formalism.BasicNotions.Loc.OL
  exact (integralClosure ℤ_[l] LL).algebraMap_mem _

def negTwist (P : LocPrime l) (K LL : FinExt l) (e : ℕ) : ↥(GK K) →* (↥LL.1)ˣ :=
  ((cycLL (P.PD K) ↥LL.1)⁻¹) ^ e

theorem negTwist_mem (P : LocPrime l) (K LL : FinExt l) (e : ℕ) (g : ↥(GK K)) :
    ((negTwist P K LL e g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  have : negTwist P K LL e g = (cycLL (P.PD K) ↥LL.1 g⁻¹) ^ e := by
    simp [negTwist]
  rw [this, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ (cyc_mem P K LL _) e

def tateLat (P : LocPrime l) (K LL : FinExt l) (e : ℕ) :
    Lattice (O := ↥(OL LL)) (charRep (negTwist P K LL e)) :=
  charLat Subtype.val_injective _ fun g => ⟨⟨_, negTwist_mem P K LL e g⟩, rfl⟩

variable {P : LocPrime l} (AI : LocAinf l P)

def piS (s : ℕ) : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

def resKs {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (Y : Lat K LL) :
    Representation ↥LL.1 ↥(GK (levelField K s)) Y.V :=
  Y.ρ.comp (Subgroup.inclusion (GK_le (K := K) (K' := levelField K s) h.2.2.1))

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified
