module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha : ∀ (D : D7) (i : D.nd.Loc) (c : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), C ≤ Z1 (WKG (chiRatO D.nd i c)) → 2 ≤ c → c ≤ D.R.t → (∀ f ∈ C, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), locFun i (chiRatO D.nd i c) w hw f ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (chiRatO D.nd i c) (C) + lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c - 1 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.Cut.ShaBound.main | exact GlobalTheory.Cut.ShaBound.main | (intros; apply GlobalTheory.Cut.ShaBound.main <;> assumption)
