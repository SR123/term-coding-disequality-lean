import {test} from 'node:test';
import assert from 'node:assert/strict';
import {fetchResource} from '../app/resource-loader.ts';

const quick = {delays: [0, 0], timeoutMs: 200};
const json = value => new Response(JSON.stringify(value));

test('a transient network failure recovers and bypasses the failed cache entry', async () => {
  const calls = [];
  let notices = 0;
  const data = await fetchResource('/proof', {...quick, onRetry: () => notices++, fetcher: async (_, options) => {
    calls.push(options.cache);
    if (calls.length === 1) throw new TypeError('NetworkError');
    return json({name: 'theorem'});
  }});
  assert.deepEqual(data, {name: 'theorem'});
  assert.deepEqual(calls, ['default', 'reload']);
  assert.equal(notices, 1);
});

test('temporary server errors and rate limiting recover for module text too', async () => {
  for (const status of [408, 429, 500, 503]) {
    let calls = 0;
    const data = await fetchResource('/source', {...quick, format: 'text', fetcher: async () => {
      return ++calls === 1 ? new Response('Unavailable', {status}) : new Response('theorem example : True := by trivial');
    }});
    assert.match(data, /theorem example/);
    assert.equal(calls, 2);
  }
});

test('persistent network errors stop after three attempts', async () => {
  let calls = 0;
  await assert.rejects(fetchResource('/proof', {...quick, fetcher: async () => {
    calls++;
    throw new TypeError('offline');
  }}), /offline/);
  assert.equal(calls, 3);
});

test('a missing file is reported without automatic retry loops', async () => {
  let calls = 0;
  await assert.rejects(fetchResource('/missing', {...quick, fetcher: async () => {
    calls++;
    return new Response('Not found', {status: 404});
  }}), /404/);
  assert.equal(calls, 1);
});

test('an incomplete JSON response can recover on retry', async () => {
  let calls = 0;
  const data = await fetchResource('/index', {...quick, fetcher: async () => {
    return ++calls === 1 ? new Response('{"declarations":') : json({declarations: []});
  }});
  assert.deepEqual(data, {declarations: []});
  assert.equal(calls, 2);
});

test('a request that stalls before headers times out and recovers', async () => {
  let calls = 0;
  const data = await fetchResource('/proof', {...quick, timeoutMs: 10, fetcher: async (_, options) => {
    if (++calls > 1) return json({loaded: true});
    return new Promise((_, reject) => options.signal.addEventListener('abort', () => reject(options.signal.reason), {once: true}));
  }});
  assert.equal(data.loaded, true);
  assert.equal(calls, 2);
});

test('the deadline covers reading the response body, not just its headers', async () => {
  let calls = 0;
  const data = await fetchResource('/proof', {...quick, timeoutMs: 10, fetcher: async (_, options) => {
    if (++calls > 1) return json({loaded: true});
    return {ok: true, json: () => new Promise((_, reject) => {
      options.signal.addEventListener('abort', () => reject(options.signal.reason), {once: true});
    })};
  }});
  assert.equal(data.loaded, true);
  assert.equal(calls, 2);
});

test('leaving a proof cancels its in-flight request without retrying', async () => {
  const controller = new AbortController();
  let calls = 0;
  const pending = fetchResource('/old-proof', {...quick, signal: controller.signal, fetcher: async (_, options) => {
    calls++;
    return new Promise((_, reject) => options.signal.addEventListener('abort', () => reject(options.signal.reason), {once: true}));
  }});
  controller.abort();
  await assert.rejects(pending, {name: 'AbortError'});
  assert.equal(calls, 1);
});

test('cancellation during backoff prevents another request', async () => {
  const controller = new AbortController();
  let calls = 0;
  await assert.rejects(fetchResource('/old-proof', {...quick, signal: controller.signal,
    onRetry: () => controller.abort(), fetcher: async () => {
      calls++;
      throw new TypeError('offline');
    }}), {name: 'AbortError'});
  assert.equal(calls, 1);
});

test('an already-cancelled request never starts', async () => {
  const controller = new AbortController();
  controller.abort();
  await assert.rejects(fetchResource('/proof', {...quick, signal: controller.signal, fetcher: async () => {
    assert.fail('A cancelled navigation must not fetch');
  }}), {name: 'AbortError'});
});

test('a manual retry starts with a fresh fetch', async () => {
  await fetchResource('/proof', {...quick, fresh: true, fetcher: async (_, options) => {
    assert.equal(options.cache, 'reload');
    return json({loaded: true});
  }});
});
