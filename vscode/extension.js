const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

/**
 * @type {LanguageClient}
 */
let client;

/**
 * Extension activation code.
 *
 * @param {vscode.ExtensionContext} context
 */
function activate(context) {
    client = new LanguageClient(
        "compiler",
        {
            run: {
                command: "/home/tdeo/repos/github.com/tadeokondrak/compiler/target/debug/lsp",
                transport: TransportKind.stdio,
            },
            debug: {
                command: "/home/tdeo/repos/github.com/tadeokondrak/compiler/target/debug/lsp",
                transport: TransportKind.stdio,
            },
        },
        { documentSelector: [{ scheme: 'file', language: 'compiler' }] },
        true
    );

    client.start();

    vscode.commands.registerCommand("compiler.restartLanguageServer", () => {
        client.restart();
    })
}

/**
 * Extension deactivation code.
 */
function deactivate() { }

module.exports = {
    activate,
    deactivate,
};
