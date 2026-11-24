module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
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

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLocMem_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocMem := by
  intro hIC hLC E _ _ _ n S Kw w hw hcw y
  obtain ⟨-, hap, -, -, hcc, -⟩ := hLC E n w hw
  have hsim : sim (loc hw y) ∈ ZU := by
    rw [sim_loc]; exact ZU.one_mem
  have hone : ∀ u, u ≠ w → u ≠ cj w → comp u (loc hw y) = 1 := fun u h1 h2 =>
    comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y
  refine ⟨fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩, fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩⟩
  · intro u hu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
      rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    have h1 : u ≠ w := fun h => hu (h ▸ hwS)
    have h2 : u ≠ cj w := fun h => hcu (by rw [h, hcc]; exact hwS)
    rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
  · intro u hu
    have h1 : u ≠ w := fun h => hwS (h ▸ hu)
    have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
    rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · by_cases h2 : u = cj w
      · subst h2
        exact hIC E n (loc hw y) w hsim (by rw [comp_loc]; exact hy)
      · rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
