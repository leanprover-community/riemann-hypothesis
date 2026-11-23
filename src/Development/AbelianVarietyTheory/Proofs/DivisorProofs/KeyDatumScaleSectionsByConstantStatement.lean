module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumScaleSectionsByConstant
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyDatum_scale_sections_by_constant : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec) (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th), (∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  first | exact @GlobalTheory.KeyEven.keyOn_scale | exact GlobalTheory.KeyEven.keyOn_scale | (intros; apply GlobalTheory.KeyEven.keyOn_scale <;> assumption)
