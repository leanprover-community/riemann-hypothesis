module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFrameRootOrigin
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_generic_frame_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) (V : ValuationSubring RM.Ω), letI := Small.cstAlg Or; ∀ (ψ : C.R →ₐ[c.F] RM.Ω) (z : FrPt Xo c RM.Ω) (d : Ix Dw → (RM.Ω)ˣ), FrMap ψ C.y z → FrBor d Fr.y₀ z → (∀ x, ψ x ∈ V) → ∀ cc : (k : RM.K) → RM.ι k, (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → (∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, cc k⟩ ∈ V) → ∀ r : RootIx Dw, ∃ v : Vˣ, ((d (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r : (RM.Ω)ˣ) : RM.Ω) = ((v : V) : RM.Ω) * ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) * Or.e r) := by
  first | exact @ModelDimension.generic_frame_root_origin | exact ModelDimension.generic_frame_root_origin
