module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OrbitFiniteR : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤

def RowLatExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u : D.what₂.Word), ∃ Λ, IsRowLat D (T.X.Fu u) Λ

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cExpl_pos' (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (hne : what₂.Nonempty) :
    0 < cExpl D F0 what₂ := by
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hc := (Formalism.L2.SG.Pf.Asm.cMass_spec hK hF (D.R.k - 1) (by omega)).1
  have hd : 0 < |(NumberField.discr D.host.F : ℝ)| ^
      (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
    apply zpow_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hL : 0 < ∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← lValEta_eq_lValEtaF hK hF i hi2]
    exact lValEta_pos hK i hi2
  have hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂ := by
    intro Λ hΛ
    exact _root_.PI.AutLzFinite.SlopeTestRemainingChoices.autLzFin_main D (D.sp.Y_sig 0) (D.mem u).A.T (D.mem u).A.T_prime.pos F0 Λ (hR.1 Λ hΛ)
  have hm := Formalism.L2.SG.PairVal.massRows_pos D F0 what₂ hA hne
  unfold cExpl
  positivity


end Formalism.L2.SG.Pf.Cnt
