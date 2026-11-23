module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PointRepAboveL

noncomputable section

namespace UpperTheory.GalS

theorem compatR (D : D7) (h0 : SumRepresentations.tie0 D) (h2 : AutomorphicGaloisAdmissible D.nd D.naut) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (hP : D.naut.ptV i P = some x)
    (hB : IsBCV D.nd D.naut i P Pa) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hn : Nc D.nd D.naut (isoLoc D.nd D.naut Pa w)) :
    D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
    UpperTheory.GalN.RelA D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)
      (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
    ∀ τ, InducesW D.nd i τ w →
      D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  obtain ⟨ρ, hc, hs, hwd, hl⟩ := isoRep D h0 h2 i P Pa hB
  obtain ⟨Pm, hPm⟩ := rep_conj D h5 i r hr x P Pa hP hB ρ hc hs hwd
  obtain ⟨-, hconj, -, -⟩ := h0.2.2.2.2.2 i
  obtain ⟨hdR, hWD, hJ⟩ := hconj _ ρ _ hc Pm hPm
  refine ⟨(hdR w hw).2 (hl w hw hn).1, ?_, fun τ hτ => ?_⟩
  · rw [hWD w (Or.inr (hl w hw hn).1)]
    exact (hl w hw hn).2.1
  · rw [hJ τ (fun w' h' => by rw [place_unique hτ h']; exact (hl w hw hn).1)]
    exact (hl w hw hn).2.2 τ hτ

end UpperTheory.GalS

end
