module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPowStatement
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tower_pf :
    UpperTheory.Gal.Gen.CongSub → UpperTheory.Gal.Gen.Tower := by
  intro hC E _ _ w a l hl hw ha N hN
  obtain ⟨m, -, J', lam, hJo, hJc, hJN, hJtf, -, -⟩ := GlobalTheory.T.exists_supercuspidal_type_character_zmod_pow E w a l hl hw ha N hN 0
  obtain ⟨J, hT, hp⟩ := hC E w a l hl hw
  obtain ⟨s, hs⟩ := hT.small _ (hJo.mem_nhds J'.one_mem)
  refine ⟨fun n => J (s + n), ⟨fun n => hT.isOpen _, fun n => hT.compact _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact hT.anti (Nat.add_le_add_left hij s)
  · intro n g hg x hx
    exact hT.normal (s + n) g (hT.anti (Nat.zero_le (s + 0)) hg) x hx
  · intro M hM
    obtain ⟨n, hn⟩ := hT.small M hM
    exact ⟨n, fun x hx => hn (hT.anti (Nat.le_add_left n s) hx)⟩
  · exact fun x hx => hJN (hs hx)
  · exact fun g hg ho => hJtf g (hs hg) ho
  · intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ, pow_mul]
      exact hp (s + n) _ ih
