import { Set } from './immutable.es.js';
import { HistoryItem } from './history.js';

export class Suspension {
  constructor(id, constrId, args) {
    this.constrId = constrId;
    this.args = args;
    this.id = id;
    this.stored = false;
    this.alive = true;
    this.history = Set().asMutable();
  }

  addToHistory(rule, ids) {
    this.history.add(new HistoryItem(rule, ids));
  }

  notInHistory(rule, ids) {
    return this.history.has(new HistoryItem(rule, ids)) == false;
  }
}
