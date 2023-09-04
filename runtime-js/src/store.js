import { Suspension } from './suspension.js';

export class Store {
  constructor (constrIdCount) {
    this.counter = 0;
    this._index = new Array(constrIdCount);
    this._initStore(constrIdCount);
  }

  _initStore(constrIdCount) {
    for(let i = 0; i < constrIdCount; i++) {
      this._index[i] = new Set();
    }
  }

  create(constrId, args) {
    this.counter++;
    return new Suspension(this.counter, constrId, args);
  }

  store(s) {
    s.stored = true;
    this._index[s.constrId].add(s);
  }

  kill(s) {
    this._index[s.constrId].delete(s);
  }

  killLate(s) {
    s.alive = false;
  }

  alive(s) {
    return s && s.alive;
  }

  lookup(constrId) {
    return this._index[constrId];
  }

  addToHistory(rule, suspensions) {
    let susp = suspensions[0];
    susp.addToHistory(rule, suspensions);
  }

  notInHistory(rule, suspensions) {
    let susp = suspensions[0];
    return susp.notInHistory(rule, suspensions);
  }

  dump() {
    console.log(this);
  }
}
