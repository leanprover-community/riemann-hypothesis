module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem isMatF_of_isMat {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
    (θ : H.Γ → Formalism.ConjugateSelfDual.Qbar l) {d : ℕ} (ρ₁ : (Ω ≃ₐ[k] Ω) →* Matrix.GeneralLinearGroup (Fin d) (Formalism.ConjugateSelfDual.Qbar l))
    (h : UpperTheory.Gal.Int.Geo.IsMat l H Ω (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁)
    (f : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Formalism.ConjugateSelfDual.Qbar l)) (hf : ∀ σ, (ρ₁ σ).val = f σ) :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.IsMatF H Ω θ f := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun σ j => ?_⟩
  rw [hb σ j, hf σ]

theorem UpperTheory.Gal.G3.jLocalMat :
    UpperTheory.Gal.Seam.NiceBc → UpperTheory.Gal.Seam.HopEx → UpperTheory.Gal.Seam.LocTower → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LocalMat := by
  intro hNice hHop hLoc E Ω _ _ _ _ _ l _ H θ hN Gw O _ _ _ Bw τK hτ
  refine ⟨fun g => ⟨_, hHop l _ _ (UpperTheory.Gal.Int.Geo.bcAlong H τK) (hNice _ _ τK H hN) g⟩, ?_⟩
  intro d ρ hρ
  obtain ⟨ρ₁, hρ₁, hc⟩ := hLoc l E _ Ω (Formalism.ConjugateSelfDual.Qbar l) τK Bw.j (fun x => (hτ x).symm) H hN
    (Formalism.ConjugateSelfDual.Qbar l) θ d ρ hρ
  refine isMatF_of_isMat (UpperTheory.Gal.Int.Geo.bcAlong H τK) (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁ hρ₁ _
    (fun σ => congrArg Units.val (hc _ σ (fun x => ?_)))
  rw [← Bw.e_comm]
  erw [MulEquiv.apply_symm_apply]
  rfl
