module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem blockGL_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := by
  intro E _ _ m r S h hh w hw
  have hmap : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
      (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
        (Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) h) :=
    Units.ext (GroundTheory.Automorphic.FourierWhittaker.map_blockMat _ _ (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))
  rw [hmap, hh w hw, map_one]

end GlobalTheory.SchurExt
