module

public import Mathlib
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.HermitianLattices.StatementMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.AdmissibleBoundsFromSource

export Formalism.MainNotions.S.UnitaryVolumeMass (f3 Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped InnerProductSpace nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7) (large₂ : SizeData₂ D)

def Gam : ℝ := (D.mem D.u₀).A.GamP

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def eta0 : ℝ := large₂.sc.b ^ (-(6 : ℝ))

def xK : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))
end Letters

section Hyp

variable (D : D7) (large₂ : SizeData₂ D)

def hyp (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

def CountTheoremHypotheses (n0 : ℕ) (A C cb : ℝ) : Prop :=
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  n0 ≤ D.R.r ∧ (D.R.rS + 1) ^ 2 ≤ D.R.r ∧
  Real.log (Real.log D.host.rdE) ≤ (D.R.r : ℝ) ∧
  (∀ (τ : D.what₂.Tau) (i : Fin D.R.r), |lamS D.R (D.hc τ) i| ≤ large₂.sc.b ^ 2) ∧
  gg D ≤ large₂.sc.b ^ A ∧ 4 * D.R.r < D.host.g 0 ∧ SplitsE D (D.host.g 0) ∧
  (∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.GapAtLeast (epsS D.R) (lamS D.R (D.hc τ))
    (C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE))) ∧
  Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) ∧ 2 ≤ large₂.sc.b ∧
  Real.log (Real.log large₂.sc.b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)

end Hyp

structure AdmC where

  A5 : ℝ
  cL : ℝ

  cN : ℝ
  CN : ℝ

  CE : ℝ

  CA : ℝ
  CA' : ℝ
  Ce : ℝ

  n7 : ℕ
  A7 : ℝ
  C7 : ℝ
  cb7 : ℝ
  c7 : ℝ

  ep0 : ℝ
  CV : ℝ

  C1 : ℝ
  C2 : ℝ
  c5 : ℝ

section admitted

variable (D : D7) (large₂ : SizeData₂ D)

def adm10 (n0 : ℕ) (A C cb c : ℝ) : Prop := CountTheoremHypotheses D large₂ n0 A C cb →
  |Dall D - Dst D| ≤ Real.exp (-(c * D.R.r * D.R.f * Real.log D.R.r)) * Dst D

end admitted

section Conclusion₂

variable (D : D7) (large₂ : SizeData₂ D)

def Conclusion1 : Prop :=
  (∀ u u' : D.what₂.Word, u ≠ u' → Kpp D u u' = 0) ∧
  (∀ u, hsNormSq (Kpp D u u) ≤ du D u * xK D) ∧
  (∀ u u' : D.what₂.Word, u ≠ u' →
    hsNormSq (Kmat D.s u u' - Kpp D u u') ≤ (1 + eta0 D large₂) * du D u * du D u' / Dst D) ∧
  (∀ u, hsNormSq (Kmat D.s u u - Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤
    Gam D * du D u ^ 2 / Dst D)

end Conclusion₂

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.AdmissibleBoundsFromSource
