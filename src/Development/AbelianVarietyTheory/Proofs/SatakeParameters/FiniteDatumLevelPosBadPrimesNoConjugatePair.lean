module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BadPrimes

theorem mapPrime_conjugate {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    seamP s (conjPrime₂ P) = conjPrime₂ (seamP s P) := by
  apply HeightOneSpectrum.ext
  ext r
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
  have hc : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) :=
    RingOfIntegers.ext ((bridge_star_holds D.R D.host (s.iE x)).trans (hs.2 (x : X.E)).symm)
  rw [mem_conjP, hc, mem_seamP, mem_seamP, mem_conjP]

theorem lev_pos_and_noConj :
    UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie
  obtain ⟨hSS, hlev, -⟩ := (isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop
  refine ⟨?_, ?_⟩
  · rw [hlev]
    have hprod : 0 < ∏ P : rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1 :=
      Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.mul_pos (pow_pos hprod _) (Nat.mul_pos (t.pr_ok.T_prime _).pos (pow_pos hprod _))
  · intro Q hQ hQ'
    obtain ⟨P, rfl⟩ : ∃ P, seamP t.seam P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).surjective Q
    rw [← mapPrime_conjugate t.seam t.seam_ok, mem_ssRec, hSS] at hQ'
    rw [mem_ssRec, hSS] at hQ
    exact sall_noConj t.sel (t.tup μ) hP.fields t.pr_ok hP.sel (t.word u) hP.avoid.2 hP.avoid.1 P hQ hQ'

end GlobalTheory.BadPrimes
