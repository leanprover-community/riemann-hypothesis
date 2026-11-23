module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section
namespace GlobalTheory.TwLevRed

theorem reGL_symm_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem blockTri_iff_mem_lev : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  intro E _ _ k _ _ _ _ PP ι hPP K T s j d hd δ hδ η n e he x hx R hR
  have hent : ∀ a b, R.val a b = 0 ↔ valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a))
      (stdOrd (Fin K) (Fin T) j d hd (e.symm b))) < 1 := by
    intro a b
    constructor
    · intro h0
      have := hR a b 0 (by rw [h0, map_zero])
      simpa using this
    · intro hv
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (R.val a b)
      have h1 := hR a b z hz.symm
      have h2 : valuation k (ι (z : E)) < 1 := by
        have : ι (z : E) = x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) -
            (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) - ι (z : E)) := by
          ring
        rw [this]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
      rw [← hz, Ideal.Quotient.eq_zero_iff_mem]
      exact hPP z h2
  have hblk : ∀ q : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j,
      Formalism.L2.DIV.blk2 (K + (s + 1)) (e q) = Sum.elim (fun _ => 0) (fun _ => 1) q := by
    intro q
    have h := he q
    unfold Formalism.L2.DIV.blk2
    rcases q with (i | i) | p
    · have : (e (.inl (.inl i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : (e (.inl (.inr i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : ¬ (e (.inr p)).val < K + (s + 1) := by
        rw [h, not_lt]; simp only [GlobalTheory.SymBridge.zPos]
        exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      simp [this]
  have hJ : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J ↔
      ∀ (p : Fin j × Fin T) (i : Fin K ⊕ Fin (s + 1)),
        valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inl i))) < 1 := by
    change (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J ↔ _
    rw [mem_parahoric]
    have e' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x =
        (reGL (stdOrd (Fin K) (Fin T) j d hd)).symm x := by
      simp [LatFrame.conj, plainFrame]
      rfl
    rw [e', reGL_symm_mem_KO_iff]
    simp only [hx, true_and]
    rfl
  rw [hJ, Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h p i
    have := h (e (.inr p)) (e (.inl i)) (by rw [hblk, hblk]; simp)
    rw [hent] at this
    simpa using this
  · intro h a b hab
    obtain ⟨q, rfl⟩ := e.surjective a
    obtain ⟨q', rfl⟩ := e.surjective b
    rw [hblk, hblk] at hab
    rw [hent]
    rcases q with q | q <;> rcases q' with q' | q' <;> simp at hab
    simpa using h q q'

end GlobalTheory.TwLevRed
