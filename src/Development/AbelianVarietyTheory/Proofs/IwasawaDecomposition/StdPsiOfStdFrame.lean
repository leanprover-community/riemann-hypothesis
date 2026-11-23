module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.IsotPart

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : principalLevelFrame.RowPsi V n} (h : GlobalTheory.Mem.R3.StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h



theorem isot_le_part : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hC i
  obtain ⟨hcore, hSF, -, hW⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hcore.lev).1
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    intro v
    have hS : R.Sb = R.Pg := hP.char.allPl
    rw [ht]
    unfold SsetF
    rw [hQ, hS]
    simp only [Finset.union_empty, Finset.mem_image]
    constructor
    · rintro ⟨PP, h1, rfl⟩
      exact ⟨PP, h1, rfl⟩
    · rintro ⟨PP, h1, h2⟩
      exact ⟨PP, h1, HeightOneSpectrum.ext h2⟩
  have hEq : SsetF R.toRealDat (Y.tupT D.what₂.mu0) = R.SF := by
    ext v
    rw [hSF v, hSF' v]
  unfold HasEig at hE
  rw [hEq] at hE
  intro y hy
  have hy' := (Y.tied.lift.isot i π y).1 hy
  rw [Y.prtWE, Y.mjRead] at hy'
  obtain ⟨U, hU, hUy⟩ := hy'
  obtain ⟨x, hx, hxU⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hcore R.SF hSF Y.hF Y.PY Y.PW
    (stdPsi_of_stdFrame Y.stdPsi.1) (fun j => stdPsi_of_stdFrame (Y.stdPsi.2 j)) _ _ c hE i U hU
  have h1 : U = (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hUy
  have h2 : x = Y.mj.eW i y := (hcore.models.HW i (sg0 D A3.A)).1 (hxU.trans h1)
  rw [Submodule.mem_comap, ← h2]
  rw [← hW] at hx
  exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.Wc' i c) c hC) hx

end GlobalTheory.Mem.R3.IsotPart
