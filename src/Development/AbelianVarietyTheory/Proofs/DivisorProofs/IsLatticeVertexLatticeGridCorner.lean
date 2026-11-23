module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem isLattice_comap_gl {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (M : Submodule R (n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (M.comap (g.1.mulVecLin.restrictScalars R)) := by
  let e : (n → K) ≃ₗ[K] (n → K) := LinearEquiv.ofLinear g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  have h : M.comap (g.1.mulVecLin.restrictScalars R) = M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      have : e (e.symm y) ∈ M := by rw [e.apply_symm_apply]; exact hy
      exact this
  rw [h]
  refine ⟨hM.fg.map _, ?_⟩
  have h2 : ((M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) : Submodule R (n → K)) : Set (n → K)) =
      (e.symm : (n → K) →ₗ[K] (n → K)) '' (M : Set (n → K)) := rfl
  intro s hs hi
  rw [h2] at hs
  have hs' : e '' s ⊆ (M : Set (n → K)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hs hx
    simpa [← hyx] using hy
  have hi' : LinearIndepOn R id (e '' s) :=
    (linearIndepOn_id_imageₛ_iff (f := (e : (n → K) →ₗ[K] (n → K)).restrictScalars R)
      (show Function.Injective ((e : (n → K) →ₗ[K] (n → K)).restrictScalars R) from e.injective).injOn).2 hi
  have hk := hM.linearIndepOn (e '' s) hs' hi'
  have hk' := (linearIndepOn_id_imageₛ_iff (f := (e.symm : (n → K) →ₗ[K] (n → K)))
    (show Function.Injective (e.symm : (n → K) →ₗ[K] (n → K)) from e.symm.injective).injOn).2 hk
  change LinearIndepOn K id (e.symm '' (e '' s)) at hk'
  simpa [Set.image_image] using hk' 

theorem _root_.GlobalTheory.T.isLattice_vertexLattice_gridCorner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)), Submodule.IsLattice D.host.E (GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y) := by
  intro D T L sc G W S y
  have hm := D.R.two_le_m
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m)) :=
    (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
      have : D.R.m = 0 := (Node.grid.inj e).1
      omega).sd.1
  apply isLattice_comap_gl _ _
  apply Submodule.IsLattice.of_fg
  obtain ⟨c, hc, hu⟩ := Formalism.UG.P.adelstabL_upper (F := D.host.F) _ (Module.Finite.iff_fg.2 hΛ.fg)
  obtain ⟨d, hd, c', hc', hcg, hcgi⟩ := Formalism.UG.P.levelaf_exists_denom (E := D.host.E) (finG (G.V (.grid D.R.m D.R.m)) y)
  have hG := Formalism.UG.P.adelstab_entries (finG (G.V (.grid D.R.m D.R.m)) y) d c' hc' hcg
  exact Module.Finite.iff_fg.mp (Formalism.UG.P.adelstab_finite (finG (G.V (.grid D.R.m D.R.m)) y) _ c d hc hd hu hG)
