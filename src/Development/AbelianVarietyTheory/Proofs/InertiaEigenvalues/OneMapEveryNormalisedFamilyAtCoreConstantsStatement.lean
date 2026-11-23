module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstants
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → ∃ (ζ : ℂ) (z : G), IsRoot1 ζ ∧ z ∈ Subgroup.center G ∧ ∀ (t : Tp) (h : M.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (M.bad t) J' (M.Lh t) (M.gam t) (M.vol t) → ∀ (y : (R.HV i (tup t)).H) (x : M.Cl' t → VsV D i M.c'.F), Place R i (tup t) h M.c0' y x → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M t x f → ∀ g : GA D (Wc D i), ph i * R.thF i (tup t) y (v₀ i (sg0 D A)) g = ζ * T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 := by
  first | exact @GlobalTheory.SerAll.ser_at_core_constants | exact GlobalTheory.SerAll.ser_at_core_constants | (intros; apply GlobalTheory.SerAll.ser_at_core_constants <;> assumption)
