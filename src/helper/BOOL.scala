package helper

import scala.language.higherKinds

sealed trait BOOL {
  type V <: BOOL
  type NOT <: BOOL
  type AND[B <: BOOL] <: BOOL
  type OR[B <: BOOL] <: BOOL
  type IMP[B <: BOOL] <: BOOL
}

object TRUE extends BOOL {
  type V = TRUE.type
  type NOT = FALSE.V
  type OR[B <: BOOL]  = V
  type AND[B <: BOOL] = B
  type IMP[B <: BOOL] = B
}

object FALSE extends BOOL {
  type V = FALSE.type
  type NOT = TRUE.V
  type OR[B <: BOOL]  = B
  type AND[B <: BOOL] = FALSE.V
  type IMP[B <: BOOL] = TRUE.V
}
