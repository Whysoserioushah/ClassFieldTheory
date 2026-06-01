module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

@[expose] public noncomputable section

namespace CategoryTheory.ShortComplex
open Abelian
open Limits hiding im

variable {C D : Type*} [Category* C] [Category* D]

section Abelian
variable [Abelian C]

/-- The cokernel of the first map of an exact complex in an abelian category is naturally isomorphic
to the coimage of the second map.

Note that we use the extra functor `F` to avoid talking about the category of exact complex. -/
def kerIsoIm (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ gFunctor ⋙ ker C ≅ F ⋙ fFunctor ⋙ im :=
  NatIso.ofComponents (fun X ↦ {
    hom := kernel.lift (cokernel.π (F.obj X).f) (kernel.ι (F.obj X).g)
      ((F.obj X).exact_iff_kernel_ι_comp_cokernel_π_zero.mp (hF X))
    inv := kernel.lift (F.obj X).g (kernel.ι (cokernel.π (F.obj X).f)) (by
      conv_rhs => rw [← cokernel.π_desc (F.obj X).f (F.obj X).g (F.obj X).zero]
      rw [← Category.assoc, kernel.condition, zero_comp])
    hom_inv_id := by apply equalizer.hom_ext; simp
    inv_hom_id := by apply equalizer.hom_ext; simp })
    fun {X Y} φ ↦ by
      apply equalizer.hom_ext
      simp [fFunctor, gFunctor]

-- /-- The cokernel of the first map of an exact complex in an abelian category is naturally isomorphic
-- to the coimage of the second map.

-- Note that we use the extra functor `F` to avoid talking about the category of exact complex. -/
-- @[simps!] def cokerIsoCoim (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
--     F ⋙ fFunctor ⋙ coker C ≅ F ⋙ gFunctor ⋙ coim :=
--   NatIso.ofComponents (fun X ↦
--     have := (hF X).epi_kernelLift
--     cokernel.congr _ _ (by simp) ≪≫
--       cokernelEpiComp (kernel.lift (F.obj X).g (F.obj X).f (F.obj X).zero) _) sorry

end Abelian
end CategoryTheory.ShortComplex
