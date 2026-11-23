module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.FitGal


theorem galTied_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ g : _root_.Formalism.L2.NGalTiedAlt (withLoc b.L), g.fr.jE = b.jE ∧ g.mt = mtL b.L b.M ∧ g.tup = b.tp.tup ∧ Nonempty (NormalizedDataCompatibility (withLoc b.L)) ∧ Nonempty (NormalizedLocalCompatibility (withLoc b.L) (mtL b.L b.M)) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) g.lp F := by
  intro hL hLp D' b fr hfr hpht hstar hexp hsplit hcheb
  obtain ⟨Hk, hHk⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch
    b.mt hstar hexp hsplit hcheb b.big b.L b.Sp b.Au
  let lp : LPTiedPlaceholder (withLoc b.L) := ⟨⟩
  let fr' : OmFrame (withLoc b.L) := { fr with }
  have au : _root_.Formalism.L2.AUTiedAlt (withLoc b.L) lp (mtL b.L b.M) Hk.av :=
    { Hk.au with
      emb := Hk.emb }
  let g : _root_.Formalism.L2.NGalTiedAlt (withLoc b.L) :=
    { fr := fr', lp := lp, mt := mtL b.L b.M, hecke := Hk.hecke, av := Hk.av, au := au
      rational := Hk.rational, tup := b.tp.tup, level := Hk.level }
  refine ⟨g, hfr, rfl, rfl, ⟨Hk.data⟩, ⟨Hk.cover⟩, ?_⟩
  intro F hF
  refine ⟨fun i σ v w hov Dv hα => ?_⟩
  · rw [hF] at hα ⊢
    obtain ⟨α, hS, he⟩ := b.row.2 σ v w hov Dv hα
    refine ⟨α, hS, ?_⟩
    show b.L.Y.satW i σ w = _
    rw [b.Au.satW i σ w]
    exact he
end GlobalTheory.FitGal
end
end
