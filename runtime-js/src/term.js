export const Unsupported = -1;
export const TVar = 0;
export const TNumber = 1;

/**
 * A logical variable
 */
export class Var {
  constructor(id) {
    this.id = id;
  }
}

export function getType(term) {
  if(isVar(term)) {
    return TVar;
  }

  if(isNumber(term)) {
    return TNumber;
  }

  return Unsupported;
}

export function isVar(term) {
  return term.id !== undefined;
}

export function isGround(term) {
  return term.id === undefined;
}

function isNumber(term) {
  return Number.isFinite(term);
}
