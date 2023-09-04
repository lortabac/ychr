/**
 * Logic-programming features needed by YCHR
 */

import { Var, isVar } from './term.js';

export class Logic {
  /**
   * Create a new logic context
   */
  constructor() {
    this.bindings = [];
  }

  /**
   * Create a new logical variable
   */
  newVar(i) {
    return new Var(i);
  }

  /**
   * Bind a variable to a term
   *
   * @param {Var} variable
   * @param term
   */
  setBinding(v, term) {
    this.bindings[v.id] = term;
  }

  /**
   * Look up the binding of a variable
   *
   * @param {Var} variable
   * @returns null or the term the variable is bound to
   */
  lookupBinding(v) {
    return this.bindings[v.id];
  }

  /**
   * Unify two terms
   */
  unify(term1, term2) {
    let isVar1 = isVar(term1);
    let isVar2 = isVar(term2);

    if(isVar1) {
      if(isVar2) {
        // term1 and term2 are vars
        let b1 = this.lookupBinding(term1);
        let b2 = this.lookupBinding(term2);

        if(isBound(b1)) {
          if(isBound(b2)) {
            // term1 and term2 are bound
            return this.unify(b1, b2);
          } else {
            // term1 is bound, term2 is not bound
            if(term2.id !== b1.id) {
              this.setBinding(term2, b1);
            }
            return true;
          }
        } else {
          if(isBound(b2)) {
            // term1 is not bound, term2 is bound
            if(term1.id !== b2.id) {
              this.setBinding(term1, b2);
            }
            return true;
          } else {
            // neither term1 nor term2 are bound
            this.setBinding(term1, term2);
            return true;
          }
        }
      } else {
        // term1 is a var, term2 is ground
        let b1 = this.lookupBinding(term1);
        if(isBound(b1)) {
          return this.unify(b1, term2);
        } else {
          this.setBinding(term1, term2);
          return true;
        }
      }
    } else {
      if(isVar2) {
        // term1 is ground, term2 is a var
        let b2 = this.lookupBinding(term2);
        if(isBound(b2)) {
          return this.unify(b2, term1);
        } else {
          this.setBinding(term2, term1);
          return true;
        }
      } else {
        // term1 and term2 are ground
        return term1 === term2;
      }
    }
  }

  /**
   * Apply the bindings to a term
   * and get the instantiated term
   */
  applyBindings(term) {
    let visited = new Set();
    return this.applyBindings_(visited, term);
  }

  applyBindings_(visited, term) {
    if(isVar(term)) {
      let id = term.id;
      if(visited.has(id)) {
        return false;
      }

      let b = this.lookupBinding(term);
      if(isBound(b)) {
        visited.add(id);
        return this.applyBindings_(visited, b);
      } else {
        return term;
      }
    } else {
      return term;
    }
  }
}

function isBound(b) {
  return b !== undefined;
}
