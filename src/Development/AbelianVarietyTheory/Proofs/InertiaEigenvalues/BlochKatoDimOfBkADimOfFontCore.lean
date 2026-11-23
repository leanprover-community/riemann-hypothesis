module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

theorem blochKatoDim_of_bkADim_of_fontCore (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (h1 : LocalSituation.bkADim (P.PD K)) (h2 : LocalSituation.fontCore (P.PD K))
    (hO : GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL)) : BlochKatoDim (P.PD K) ↥LL.1 := by
  unfold LocalSituation.bkADim at h1
  unfold LocalSituation.fontCore at h2
  unfold BlochKatoDim
  intro hs V _ _ _ _ _ _ _ _ _ ρ hc hcrys
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := V, ρ := ρ, cont := hc, modO := Module.compHom V (algebraMap ↥(OL LL) ↥LL.1),
      towO := by
        letI : Module ↥(OL LL) V := Module.compHom V (algebraMap ↥(OL LL) ↥LL.1)
        exact ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩ }
  have hF := h2 ↥LL.1 ↥(OL LL) hO A
  have hE := h1 ↥LL.1 ↥(OL LL) hO A (hF.2.2 hcrys)
  have hfin := hF.2.1.1
  dsimp only [A] at hE hfin
  obtain ⟨e1, e2⟩ := DeRhamSplit.main l P K LL hs V ρ hfin
  rw [hE, e1, e2 0]
  push_cast [Finset.sum_sub_distrib]
  ring

end GlobalTheory
