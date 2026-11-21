import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.Dual

theorem finAt_ti {n : ℕ} (v : Pl) (g : GL (Fin n) 𝔸[ℚ]) :
    finAt v (ti g) = GL2LocalData.tinv (finAt v g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := congrArg (fun x : GL (Fin n) (Qv v) => x.val j i) (Reduction.finAt_inv v g)
  exact h








local notation "rP" => GroundTheory.Automorphic.GL2Classical.realPart






end GlobalTheory.CompanionTheory.GL2Factorization.Dual
