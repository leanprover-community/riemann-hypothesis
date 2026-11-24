module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBC_of :
    TrChar → FamBC → WtBC → RpBasic → RpOp → TrBC := by
  intro hChar hFam hWbc hRp hOp q _ n i Z' S' Z S v p' p g _ w hpb hw hq x
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWbc v p' p g w hpb hw
  have hq' : IsUnit ((q : ℕ) : Γ(S', ⊤)) := by
    have := hq.map g.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hs, _⟩ := hChar q i p w hw hq
  obtain ⟨τ', hτ', hτeq⟩ := hFam q i v p' p g w hpb (trFam p w q i) hs
  rw [(hChar q i p w hw hq).2.2 _ hs n, (hChar q i p' _ hw' hq').2.2 τ' hτ' n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) _ Z n).1 x
  have h1 := hOp _ _ (trFam p w q i) n x a ha
  have h2 := (hRp (ZMod q) _ S n).2.2.2.1 S' g _ _ h1
  have h3 := (hRp (ZMod q) _ Z n).2.2.2.1 Z' v x a ha
  have h4 := hOp _ _ τ' n _ _ h3
  have h5 : Rp ((τ'.op n) ((cpull ((chains (ZMod q)).map (sch.map v)) (res (ZMod q) (tw q i)) n) x))
      (Sec.res g ((((trFam p w q i).deg n).app (Sq.self p)) a)) := by
    have e := hτeq n a
    exact e ▸ h4
  exact ((hRp (ZMod q) _ S' n).2.2.1 _ _ _ _ h2 h5).2.1 rfl
