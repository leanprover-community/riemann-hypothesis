module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.kerOpen_pf :
    UpperTheory.Gal.Gen.PowNhds → UpperTheory.Gal.Gen.KerOpen := by
  intro hP E _ _ w a J hJ A _ _ θ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hV := hP E w a (Nat.card A) hN (J : Set (GL (Fin a) (w.adicCompletion E)))
    (hJ.mem_nhds J.one_mem)
  refine ⟨interior ((fun x => x ^ Nat.card A) '' (J : Set (GL (Fin a) (w.adicCompletion E)))),
    isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := interior_subset hx
  have hx' : x = (⟨y, hy⟩ : J) ^ Nat.card A := Subtype.ext (by simpa using hxy.symm)
  rw [hx', map_pow, pow_card_eq_one']
