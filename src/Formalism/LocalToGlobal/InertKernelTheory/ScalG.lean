module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

def expG (X : Sys p) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℤ :=
  ∑ v : X.Pl, X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2)

def scalG (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℂ :=
  muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j La))⁻¹ *
    (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j La)) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ))

end Formalism.L2.KerInert.KG
