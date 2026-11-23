module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitStab
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.G

theorem self_dual_lattice_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ) (hfin : Module.Finite (𝓞 E) Lb)
    (hint : ∀ x ∈ Lb, ∀ y ∈ Lb, Formalism.UG.hform (σ : E →+* E) J x y ∈ Formalism.UG.intOE E)
    (hdual : ∀ y : Fin n → E, (∀ x ∈ Lb, Formalism.UG.hform (σ : E →+* E) J x y ∈ Formalism.UG.intOE E) → (T : E) • y ∈ Lb)
    (hT : (T : 𝓞 F) ∉ v.asIdeal) : SelfDualAt σ J v Lb :=
  self_dual_local F E n σ J v Lb T hfin hint hdual hT

end Formalism.L2.G
