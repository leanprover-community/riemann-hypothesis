import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PsiGeOn

noncomputable section

namespace GlobalTheory.Core.AtG

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable (D : D7) (EX : ErrX D) (u : D.what₂.Word)

def vDeg (i : Fin 2) (w : D.what₂.places.Pl) : ℝ := ∑ j ∈ Finset.Icc 1 D.R.m, vNN EX i u j w

def errF (D : D7) : ℝ := (D.R.f : ℝ) * D.R.m * (D.R.N D.R.m : ℝ) ^ 2

def errA (D : D7) : ℝ := errF D + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ)

def Big : Prop :=
  ∀ i : Fin 2, 2 * D.R.f * D.R.N D.R.m + 1 < D.host.g i ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, (∑ τ : D.what₂.Tau, nuAbs D u j τ) + 1 < (D.host.g i : ℝ)

def ColA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errF D)

def PsiA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    Int.PsiGeOn D u (DV.MramL D u) w ((D.what₂.places.ramIdx w : ℝ) * (-vDeg D EX u i w - errA D))

def PerA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    Int.PerGeOn D u (DV.MramL D u) w ((D.what₂.places.ramIdx w : ℝ) * (-vDeg D EX u i w - errA D))

def DegExact : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.m, ∀ τ : D.what₂.Tau,
    nuAbs D u j τ =
      (∑ a : Fin D.R.k, (((D.hcW u τ).u a : ℝ) - ((D.R.k : ℝ) + 1 - 2 * ((a : ℝ) + 1)) / 2)) +
        (D.R.k : ℝ) * (wj D j τ - (D.R.k : ℝ) / 2 - (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) / 2) +
        ((D.R.t : ℝ) + 1) * ∑ i ∈ Finset.Ico 1 j, (wj D j τ - wj D i τ - ((j : ℝ) - i) * ((D.R.t : ℝ) + 1))

def UnitSum : Prop :=
  ∀ (i : Fin 2), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ S : Finset D.what₂.places.Pl,
    (∀ w, w ∈ S ↔ D.what₂.places.resChar w = D.host.g i) →
    ∑ w ∈ S, 2 * lw D.what₂.LL (D.plEq w) * ((D.what₂.places.ramIdx w : ℝ) * vNN EX i u j w) =
      (∑ τ : D.what₂.Tau, nuAbs D u j τ) * Real.log (D.host.g i : ℝ)

def DegLe (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.m,
    (∑ τ : D.what₂.Tau, nuAbs D u j τ) ≤ (∑ t : D.host.TT, (L.aT t : ℝ)) + (D.R.k : ℝ) * (∑ τ : D.what₂.Tau, wj D j τ) +
      C * (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * (L.etaSz + D.R.t))


def errStep (D : D7) : ℝ :=
  ∑ j ∈ Finset.range D.R.m, ((D.R.f : ℝ) * (D.R.N j : ℝ) * (D.R.N (j + 1) : ℝ) +
    2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ))

def ColStep : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errStep D)

def ColCoarse : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errA D)






example : ∑ j ∈ Finset.range 2, ((5 + j * 8) * (5 + (j + 1) * 8) + 2 * 2 ^ 2 * 21) = 674 ∧ 2 * 21 ^ 2 = 882 := by decide

example (D : D7) : errA D - errF D = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) := by unfold errA; ring

end GlobalTheory.Core.AtG
