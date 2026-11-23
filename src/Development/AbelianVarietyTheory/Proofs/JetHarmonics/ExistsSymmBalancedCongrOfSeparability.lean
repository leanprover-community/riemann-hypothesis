module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

@[expose] public section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem exists_addHom_tensor_int_of_biadditive {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M → N → P) (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n)
    (h2 : ∀ m n n', f m (n + n') = f m n + f m n') :
    ∃ g : M ⊗[ℤ] N →+ P, ∀ m n, g (m ⊗ₜ[ℤ] n) = f m n := by
  let F : M →+ N →+ P := AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)
  refine ⟨TensorProduct.liftAddHom F (fun r m n => ?_), fun m n => ?_⟩
  · rw [map_zsmul, map_zsmul]; rfl
  · rw [TensorProduct.liftAddHom_tmul]; rfl

end GlobalTheory
