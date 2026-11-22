module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def deltaR (c : ℕ) (g : GL n k) : ℝ := nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1)

def IsCosetFn (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) (f : GL (n ⊕ Fin c) k → ℂ) : Prop :=
  (∀ u ∈ N k n c 1, ∀ (g : GL n k) (x : GL (n ⊕ Fin c) k), f (u * embX c g * x) = (deltaR c g : ℂ) * f x) ∧
    (∀ x, ∀ j ∈ J, f (x * j) = f x) ∧
    ∀ x, DoubleCoset.mk (R k n c 1) J x ≠ DoubleCoset.mk (R k n c 1) J h → f x = 0

def IsCO {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) : Prop :=
  IsOpen (J : Set G) ∧ IsCompact (J : Set G)

def IsUnif (ϖ : kˣ) : Prop := ∀ x : k, valuation k x < 1 ↔ valuation k x ≤ valuation k (ϖ : k)

variable [MeasurableSpace k] [BorelSpace k]

def volR (ν : Measure k) (m : Measure (GL n k)) (S : Subgroup (GL (n ⊕ Fin c) k)) : ℝ≥0∞ :=
  ∫⁻ g, volN ν n c 1 {u : N k n c 1 | embX c g * (u : GL (n ⊕ Fin c) k) ∈ S} ∂m

def rescale (ν : Measure k) (b : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) : Measure (GL n k) :=
  (volN ν n c 1 ((stabLat b).subgroupOf (N k n c 1)))⁻¹ • m

end Defs

section Levels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Reduces {a : Type} [Fintype a] [DecidableEq a] (g : GL a k) (gb : GL a 𝓀[k]) : Prop :=
  ∃ g₀ : GL a 𝒪[k], Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀ = g ∧
    Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀ = gb

def IsUpperUnip {F a : Type} [Field F] [DecidableEq a] (pos : a → ℕ) (M : Matrix a a F) : Prop :=
  ∀ r s, pos s ≤ pos r → M r s = (1 : Matrix a a F) r s

def superSum {F a : Type} [Field F] [Fintype a] (pos : a → ℕ) (M : Matrix a a F) : F :=
  ∑ r, ∑ s, if pos s = pos r + 1 then M r s else 0

def framePos (κ l : ℕ) : Fin κ ⊕ Fin l → ℕ := Sum.elim (fun i => i.val) (fun i => κ + i.val)

def IsSymLevel (ψ : AddChar k Circle) (ϖ : kˣ) (ρ : ℕ) {κ l : ℕ} (P : TypeDatum k (Fin κ ⊕ Fin l)) : Prop :=
  (∀ g, g ∈ P.J ↔ ∃ u ∈ N 𝓀[k] (Fin κ) l (ρ + 1), ∃ γ : GL (Fin κ) 𝓀[k],
      IsUpperUnip Fin.val γ.val ∧ Reduces g (u * embX l γ)) ∧
    ∀ g : P.J, (P.lam g : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum (g : GL (Fin κ ⊕ Fin l) k)) *
      ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁)

def colPos (κ : ℕ) (t : Type) : XIx (Fin κ) t 0 → ℕ :=
  Sum.elim (Sum.elim (fun i => i.val) (fun i => i.elim0)) (fun p => p.1.elim0)

variable (k) in
def colGroup (κ : ℕ) (t : Type) [Fintype t] [DecidableEq t] : Set (GL (XIx (Fin κ) t 0) k) :=
  {γ | ∃ gb, Reduces γ gb ∧ IsUpperUnip (colPos κ t) gb.val}

def colChar (ψ : AddChar k Circle) (ϖ : kˣ) {κ : ℕ} {t : Type} [Fintype t] [DecidableEq t]
    (γ : GL (XIx (Fin κ) t 0) k) : ℂ :=
  ψ ((ϖ⁻¹ : kˣ) * superSum (colPos κ t) γ.val)

end Levels

section Props
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

def StepWellDefined : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ), 1 ≤ c →
  ∀ (μ : kˣ →* ℂˣ) (P' : Level (GL (n' ⊕ Fin (c + 1)) k)) (P : Level (GL (n ⊕ Fin c) k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ ∈ SB _ → IsCO P'.J → IsCO P.J → HasTypes μ P' P Φ →
    (∀ h' h, flat ψ ν μ Φ h' h ∈ SB (Matrix n n' k)) ∧
    (∀ h', (idxAt ψ ν μ Φ P.J h').Finite) ∧
    (∀ u' ∈ N k n' (c + 1) 1, ∀ (g' : GL n' k) (j' : P'.J) h' h,
      flat ψ ν μ Φ (u' * embX (c + 1) g' * h' * (j' : GL (n' ⊕ Fin (c + 1)) k)) h =
        ((P'.lam j' : ℂ) * (ψ (simpleSum u') : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g') ^ ((c : ℝ) / 2) : ℝ) : ℂ)) • om μ g' 1 (flat ψ ν μ Φ h' h)) ∧
    (∀ u ∈ N k n c 1, ∀ (g : GL n k) (j : P.J) h' h,
      flat ψ ν μ Φ h' (u * embX c g * h * (j : GL (n ⊕ Fin c) k)) =
        ((((P.lam j)⁻¹ : ℂˣ) : ℂ) * (ψ (-simpleSum u) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - 1) : ℝ) : ℂ)) •
            om μ 1 g (flat ψ ν μ Φ h' h)) ∧
    (∀ h₁' h₂' h₁ h₂, DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₁' = DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₂' →
      DoubleCoset.mk (R k n c 1) P.J h₁ = DoubleCoset.mk (R k n c 1) P.J h₂ →
      (flat ψ ν μ Φ h₁' h₁ ≠ 0 ↔ flat ψ ν μ Φ h₂' h₂ ≠ 0)) ∧
    (∀ h₁' h₂', DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₁' = DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₂' →
      idxAt ψ ν μ Φ P.J h₁' = idxAt ψ ν μ Φ P.J h₂') ∧
    ∀ b h' h, xi ψ ν μ Φ P.J b h' h ≠ 0 ↔ DoubleCoset.mk (R k n c 1) P.J h ∈ idxAt ψ ν μ Φ P.J h'

def ChainFinite : Prop :=
  ∀ (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z), T.Regular → T.Laws →
    (∀ j c (h : j + 1 + c = s) g g', T.entry ψ ν j c h g g' ≠ 0 ↔
      DoubleCoset.mk (R k (X (j + 1)) (c + 1) 1) (T.lev (j + 1) (c + 1) (congrArg (· + 1) h)).J g' ∈ T.idx ψ ν j c h g) ∧
    ∀ A : RepFam k s X, T.IsRepSystem A ψ ν →
      (∀ j c h, (A j c h).Finite) ∧
      (∀ A' : RepFam k s X, T.IsRepSystem A' ψ ν → ∀ j c (h : j + c = s),
        DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A j c h =
          DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A' j c h) ∧
      (∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ T.Adapted A (box _ (ϖ ^ e)⁻¹) (box _ (ϖ ^ e))) ∧
      ∀ c₁ c₂ : kˣ, (T.coupIdx A (box _ c₁) (box _ c₂)).Finite

def CosetMeasure : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
  ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k,
    IsCO (prX (Cgrp J h)) ∧
    (∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1) ∧
    (∃ f, IsCosetFn J h f ∧ f h = 1) ∧
    ((resCard k).Prime → ∀ b, ∃ z : ℤ, volNat ν b (Cgrp J h) = (resCard k : ℝ) ^ z) ∧
    ∀ (m : Measure (GL n k)), m.IsHaarMeasure →
      volR ν m (Cgrp J h) = volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) * m (prX (Cgrp J h)) ∧
      volR ν m (Cgrp J h) ≠ 0 ∧ volR ν m (Cgrp J h) ≠ ⊤ ∧
      (∀ b, (volR ν (rescale ν b m) (Cgrp J h)).toReal = volNat ν b (Cgrp J h) * (m (prX (Cgrp J h))).toReal) ∧
      ∀ (μG : Measure (GL (n ⊕ Fin c) k)), μG.IsHaarMeasure → ∀ f, IsCosetFn J h f → ∀ z : ℂ,
        IsQuotInt ν m μG 1 f z ↔ z = (((μG J).toReal / (volR ν m (Cgrp J h)).toReal : ℝ) : ℂ) * f h

end Props

end GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
