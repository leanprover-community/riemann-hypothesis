module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pIsoEx :
    NormTwo → BlockMat → IsoEx := by
  intro hN hB E _ _ _ A n hn
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, y, hxy, hint⟩ := hN E A
  have hinv : ∀ z, cF E (cF E z) = z := fun z => GlobalTheory.CompanionTheory.OnlyStab.conjFin_invol z
  have hfix : cF E (algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) := by
    refine (conjFin_algebraMap _ _).trans (congrArg _ ?_)
    change IsCMField.complexConj E (A.c : E) = (A.c : E)
    rw [← A.bar_eq, A.c_real]
  obtain ⟨a, ha, hS⟩ := hB _ (cF E) hinv _ x y hfix hxy m
  refine ⟨a, ?_, ?_⟩
  · have hd : (Matrix.diagonal fun i => ((A.dg (2 * m + 1) i : 𝓞 E) : E)).map
        (algebraMap E (FiniteAdeleRing (𝓞 E) E)) =
        Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else
          algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [Arith.dg]
      split_ifs <;> simp
    rw [hd]
    exact ha
  · intro w q hq hg hqw
    obtain ⟨h1, h2, h3, h4⟩ := hint w q hq hg hqw
    have hc : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) ∈
        (w.adicCompletionIntegers E).toSubring.comap (pLoc E w) := by
      change Valued.v (algebraMap E (w.adicCompletion E) (A.c : E)) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (A.c : E)).trans_le
        (HeightOneSpectrum.valuation_le_one w A.c)
    have hall := hS ((w.adicCompletionIntegers E).toSubring.comap (pLoc E w)) h1 h2 h3 h4 hc
    rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
    refine ⟨fun i j => (hall i j).1, fun i j => ?_⟩
    rw [← map_inv]
    exact (hall i j).2
